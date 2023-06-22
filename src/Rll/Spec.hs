{-# LANGUAGE BangPatterns #-}
module Rll.Spec
  (
  ) where

import Rll.Ast
import Rll.Context (DataType(..), BuiltInType(..), getDataTypeName)
import Rll.Core
import Rll.TypeSub (rawTypeSub, applyTypeParams)
import Rll.SpecIR

import Data.HashMap.Strict qualified as M
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.List (foldl')
import Control.Exception (assert)
import Data.Text (Text)

-- | Eventually we will need this to hold things like the type argument
-- to a `Box`.
data SpecBuiltIn
  = SpecI64
  | SpecString
  deriving Show

-- | A specialized data type with fully concrete types.
--
-- We remove the enum name since now we've mangled it.
data SpecDataType
  = SpecEnum (M.HashMap Text [Ty])
  | SpecStruct Text [Ty]
  -- | We do a translation stage to include any type arguments to
  -- things like `Box`.
  | SpecBuiltIn SpecBuiltIn
  deriving Show

-- | A declaration that has been specialized to have fully concrete types
-- with no type variables in them.
data SpecDecl
  = SpecFun ClosureEnv (Maybe SVar) [(SVar, Ty)] SpecIR
  | SpecDataType SpecDataType
  deriving Show

data Lambda = PolyLambda
  { fix :: Maybe SVar
  , tyArgs :: [(TyVarBinding, Kind)]
  , args :: [(SVar, Ty)]
  , env :: ClosureEnv
  , body :: Core
  }
  deriving Show

-- | Various kinds of local functions that can exist
-- in the context.
data LocalFun
  = PolyLF Int Lambda
  | MonoLF MVar Var
  | TopLF Var
  deriving Show

data SpecCtx = SpecCtx
  { specDecls :: M.HashMap MVar SpecDecl
  , enclosingFun :: MVar
  -- | variables that refer to local functions.
  , localFuns :: M.HashMap Var LocalFun
  , lambdaCounter :: Int
  , coreDataTypes :: M.HashMap Var DataType
  , coreFuns :: M.HashMap Var Core
  } deriving Show

data SpecErr
  -- | Could not find the function in `coreFuns`.
  = NoCoreFun Var
  -- | You must fully apply the type arguments to a polymorphic
  -- function before you can use it as a first class value.
  | MustSpec Span
  -- | Cannot immediately specialize a polymorphic lambda function.
  --
  -- Span of the lambda.
  | NoImmediateSpec Span
  deriving (Show, Eq)

newtype Spec a = MkSpec { unSpec :: StateT SpecCtx (Except SpecErr) a }
  deriving (Functor, Applicative, Monad, MonadError SpecErr, MonadState SpecCtx)

-- | Get an unspecialized core function.
getCoreFun :: Var -> Spec Core
getCoreFun name = do
  coreFuns <- gets (.coreFuns)
  case M.lookup name coreFuns of
    Nothing -> throwError $ NoCoreFun name
    Just fun -> pure fun

-- | Substitute type arguments into a `Core`.
--
-- Takes multiple types to substitute to make it easier to use
-- when specializing a polymorphic function.
typeSubInCore :: [Ty] -> Core -> Core
typeSubInCore tyCtx = go 0 where
  -- NOTE could probably improve performance by not doing `goTy` on every
  -- type and instead building it based on structure of core and the types
  -- of descendants.
  go :: Int -> Core -> Core
  go xi core@Core{ty, span, coref} = Core (goTy ty) span $ case coref of
    AppTyCF t1 tys -> AppTyCF (f t1) $ goTy <$> tys
    LamCF fix polyB argB env t1 -> LamCF fix polyB (fmap goTy <$> argB) env $ f t1
    _ -> f <$> coref
    where
    -- Because the type arguments should have no type variables, we
    -- don't need to shift them.
    g ty (i, arg) = rawTypeSub (xi+i) arg ty
    goTy baseTy = foldl' g baseTy $ zip [0..] tyCtx
    f = go xi

-- | Utility function that checks if a declaration already
-- has been created. If it hasn't, it builds and registers
-- it.
guardDecl :: MVar -> Spec SpecDecl -> Spec MVar
guardDecl mvar act = do
  specDecls <- gets (.specDecls)
  case M.lookup mvar specDecls of
    Just _ -> pure ()
    Nothing -> do
      sd <- act
      addSpecDecl mvar sd
  pure mvar

-- | Look up a local function from the context.
lookupLocalFun :: Var -> Spec (Maybe LocalFun)
lookupLocalFun v = M.lookup v <$> gets (.localFuns)

-- | Specializes a data type and registers it under the mangled name.
--
-- Only does so once.
specDataType :: DataType -> [Ty] -> Spec MVar
specDataType dt tyArgs = guardDecl name $ pure specDt
  where
  name = mangleDataType (getDataTypeName dt) tyArgs
  specDt = SpecDataType $ case dt of
    EnumType name tyParams cases _ -> SpecEnum $
      applyTypeParams tyArgs tyParams <$> cases
    StructType con tyParams fields _ -> SpecStruct con $
      applyTypeParams tyArgs tyParams fields
    BuiltInType enum -> SpecBuiltIn $ case enum of
      BuiltInI64 -> assert (tyArgs == []) $ SpecI64
      BuiltInString -> assert (tyArgs == []) $ SpecString

-- | function for specializing the body of functions.
specExpr :: Core -> Spec SpecIR
specExpr core@Core{span, coref} = do
  case core.ty.tyf of
    Univ _ _ _ _ _ -> throwError $ MustSpec span
    _ -> pure ()
  case coref of
    LetStructCF sv mems t1 t2 -> fmap sf $ LetStructSF sv mems <$> specExpr t1 <*> specExpr t2
    ModuleVarCF v -> do
      mvar <- specFunDef v []
      pure $ sf $ ClosureSF mvar $ ClosureEnv M.empty
    LocalVarCF v -> lookupLocalFun v >>= \case
      Just _ -> sf <$> specLocalFun v []
      Nothing -> pure $ sf $ VarSF v
    RefCF v -> pure $ sf $ RefSF v
    CopyCF v -> pure $ sf $ CopySF v
    DropCF sv t1 -> fmap sf $ DropSF sv <$> specExpr t1
    -- The `Imp` stage will work out the explict thunks when
    -- partial application happens.
    AppTmCF t1 args -> fmap sf $ AppSF <$> specExpr t1 <*> traverse specExpr args
    LiteralCF lit -> pure $ sf $ LiteralSF lit
    ConCF dt v -> do
      mvar <- specDataType dt []
      pure $ sf $ ConSF mvar v
    CaseCF t1 branches -> fmap sf $ CaseSF <$>
      specExpr t1 <*> traverse (traverse specExpr) branches
    AppTyCF t1 tys -> case t1.coref of
      -- Recursive functions should be picked up here as well.
      LocalVarCF v -> sf <$> specLocalFun v tys
      ConCF dt var -> do
        mvar <- specDataType dt tys
        pure $ sf $ ConSF mvar var
      ModuleVarCF v -> do
        mvar <- specFunDef v tys
        pure $ sf $ ClosureSF mvar $ ClosureEnv M.empty
      LamCF fix polyB argB env body -> throwError $ NoImmediateSpec span
      -- NOTE: how do we handle trying to specialize a reference?
      -- I think that's automatically rejected?
      _ -> error "Can't specialize this? Not certain if this can happen."
    LetCF sv t1 t2 -> case t1.coref of
      LamCF fix polyB argB env body
        | polyB /= [] -> do
            let poly = PolyLambda fix polyB argB env body
            withPolyLambda sv.var poly $ specExpr t2
      _ -> fmap sf $ LetSF sv <$> specExpr t1 <*> specExpr t2
    LamCF fix [] argB env body -> do
      mvar <- storeLambda fix argB env body
      pure $ sf $ ClosureSF mvar env
    LamCF _ polyB _ _ _ -> error "Should be caught by MustSpec at start"
  where sf = SpecIR core.ty core.span

-- | Generate a fresh lambda name using `lambdaCounter`
-- and the types used to specialize it.
freshLambdaName :: [Ty] -> Spec MVar
freshLambdaName tys = do
  ctx <- get
  put $ ctx{lambdaCounter=ctx.lambdaCounter+1}
  pure $ mangleLambda ctx.enclosingFun tys ctx.lambdaCounter

-- | Insert a SpecDecl.
addSpecDecl :: MVar -> SpecDecl -> Spec ()
addSpecDecl mvar sd = modify' \ctx ->
  ctx{specDecls=M.insert mvar sd ctx.specDecls}

-- | Store a non-polymorphic lambda in `specDecls`.
storeLambda :: Maybe SVar -> [(SVar, Ty)] -> ClosureEnv -> Core -> Spec MVar
storeLambda fix args env body = do
  name <- freshLambdaName []
  let wrap = case fix of
        Just recName -> withLocalFun recName.var (MonoLF name recName.var)
        Nothing -> id
  body' <- wrap $ specExpr body
  addSpecDecl name $ SpecFun env fix args body'
  pure name

-- | Register and unregister a lam
withLocalFun :: Var -> LocalFun -> Spec a -> Spec a
withLocalFun v lf act = do
  entryLocals <- gets (.localFuns)
  modify' \ctx -> ctx
    {localFuns = M.insert v lf ctx.localFuns}
  val <- act
  modify' \ctx' -> ctx'{localFuns=entryLocals}
  pure val

-- | Register and unregister a polymorphic lambda function
-- in the context.
withPolyLambda :: Var -> Lambda -> Spec a -> Spec a
withPolyLambda v lam@PolyLambda{fix} act = do
  count <- gets (.lambdaCounter)
  modify' \ctx -> ctx
    {lambdaCounter = ctx.lambdaCounter + 1}
  let localFun = PolyLF count lam
      -- here we create a second entry for the recursive
      -- function name pointing to the same `LocalFun`.
      wrap = case fix of
        Nothing -> id
        Just sv -> withLocalFun sv.var localFun
  withLocalFun v localFun $ wrap act

-- | Convert the name of a local function into the appropriate
-- call to a top level definition, specializing if necessary.
specLocalFun :: Var -> [Ty] -> Spec (SpecF SpecIR)
specLocalFun lfName tyArgs = lookupLocalFun lfName >>= \case
  Nothing -> error $ "Shouldn't be possible. Error in determining if "
    <> "var is local vs module or in type checking."
  Just localFun -> case localFun of
    -- Since this lambda only has one version, we can just point to what's
    -- already compiled
    MonoLF mvar envVar -> pure $ RecClosureSF mvar envVar
    -- This is just the name of a top level function.
    TopLF v -> do
      mvar <- specFunDef v tyArgs
      pure $ ClosureSF mvar $ ClosureEnv M.empty
    PolyLF i (PolyLambda fix polyB argB env bodyCore) -> do
      enclosingFun <- gets (.enclosingFun)
      let name = mangleLambda enclosingFun tyArgs i
      guardDecl name do
        let bodyCore' = typeSubInCore tyArgs bodyCore
        body <- specExpr bodyCore'
        pure $ SpecFun env fix argB body
      pure $ ClosureSF name env

-- | Specialize a call to a top level function definition.
specFunDef :: Var -> [Ty] -> Spec MVar
specFunDef name tyArgs = guardDecl mangledName do
  -- We save the lambdas we started with, and use a blank map for
  -- when we're specializing this function, since it's separate.
  SpecCtx
    { localFuns=entryLocals
    , enclosingFun=entryEnclosingFun
    } <- get
  modify' \ctx -> ctx{ localFuns=M.empty, enclosingFun=mangledName }
  (fix, args, coreBody) <- getBody <$> getCoreFun name
  body <- specExpr coreBody
  modify' \ctx -> ctx
    { localFuns = entryLocals
    , enclosingFun = entryEnclosingFun
    }
  pure $ SpecFun (ClosureEnv M.empty) fix args body
  where
  mangledName = mangleFun name tyArgs
  getBody :: Core -> (Maybe SVar, [(SVar, Ty)], Core)
  getBody fullCore@Core{coref} = case coref of
    LamCF fix polyB argB (ClosureEnv env) body ->
      -- Top level Function definitions should never be able
      -- to capture environment variables.
      assert (env == M.empty) $
      let body' = typeSubInCore tyArgs body
      in assert (length polyB == length tyArgs) (fix, argB, body')
    _ -> (Nothing, [], fullCore)

-- | Specialize a core module.
--
-- Uses an unspecialized main function as an entry point.
specModule :: M.HashMap Var DataType -> [(Var, Core)] ->
  Either SpecErr (M.HashMap MVar SpecDecl)
specModule dataTypes coreFuns = run $ specFunDef (Var "main") []
  where
  ctx = SpecCtx
    { specDecls = M.empty
    , coreDataTypes = dataTypes
    , coreFuns = M.fromList coreFuns
    , localFuns = M.empty
    , lambdaCounter = 0
    , enclosingFun = error "Should be overriden by specFunDef"
    }
  run spec = fmap ((.specDecls) . snd) $ runExcept $ flip runStateT ctx $ unSpec spec
