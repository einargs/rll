module Rll.Spec
  ( specModule
  , SpecErr(..)
  , prettyDeclMap
  ) where

import Rll.Ast
import Rll.Context (DataType(..), BuiltInType(..), getDataTypeName, getDataConArgNum)
import Rll.Core
import Rll.TypeSub (rawTypeSub, applyTypeParams, tyIsConcrete, typeAppSubs)
import Rll.SpecIR

import Data.HashMap.Strict qualified as M
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Control.Monad (void, forM_)
import Data.Foldable (traverse_)
import Data.List (foldl', elemIndex)
import Control.Exception (assert)
import Data.Text qualified as T
import Prettyprinter
import Debug.Trace qualified as D

data Lambda = PolyLambda
  { fix :: Maybe SVar
  , tyArgs :: [(TyVarBinding, Kind)]
  , args :: [(SVar, Ty, Mult)]
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
  -- | A list of spec decls as they've been added.
  , specDeclOrder :: [(MVar, SpecDecl)]
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
  -- | Cannot find the data type in `specDecls`.
  | NoSpecDataType MVar
  -- | Cannot find the data type in `coreDataTypes`.
  | NoCoreDataType Var
  deriving (Show, Eq)

newtype Spec a = MkSpec { unSpec :: StateT SpecCtx (Except SpecErr) a }
  deriving newtype (Functor, Applicative, Monad, MonadError SpecErr, MonadState SpecCtx)

-- | Pretty print a map of declarations.
prettyDeclMap :: M.HashMap MVar SpecDecl -> Doc ann
prettyDeclMap m = vsep $ f <$> M.toList m where
  f (v, sd) = pretty v <+> pretty sd

-- | Get an unspecialized core function.
getCoreFun :: Var -> Spec Core
getCoreFun name = do
  coreFuns <- gets (.coreFuns)
  case M.lookup name coreFuns of
    Nothing -> throwError $ NoCoreFun name
    Just fun -> pure fun

-- | Lookup the core data type and throw an error if not found.
lookupCoreDataType :: Var -> Spec DataType
lookupCoreDataType v = do
  cdts <- gets (.coreDataTypes)
  case M.lookup v cdts of
    Nothing -> throwError $ NoCoreDataType v
    Just cdt -> pure cdt

-- | Utility function that takes the full type of a
-- function and uses it to annotate the arguments.
addMultToArgs :: Ty -> [(SVar, Ty)] -> [(SVar, Ty, Mult)]
addMultToArgs (Ty _ (Univ _ _ _ _ out)) rs = addMultToArgs out rs
addMultToArgs (Ty _ (FunTy m _ _ out)) ((sv, ty):rs) = (sv, ty, m):addMultToArgs out rs
addMultToArgs _ [] = []
addMultToArgs _ _ = error "function type should have been at least as long as the arg list"

-- | Substitute type arguments into a `Core`.
--
-- Takes multiple types to substitute to make it easier to use
-- when specializing a polymorphic function.
typeSubInCore :: [Ty] -> Core -> Core
typeSubInCore tyCtx coreIn = assert (all tyIsConcrete tyCtx) $ go coreIn where
  -- We assert that none of our arguments have type variables in them.
  -- NOTE could probably improve performance by not doing `goTy` on every
  -- type and instead building it based on structure of core and the types
  -- of descendants.
  go :: Core -> Core
  go core@Core{ty, span, coref} = Core (applyTyCtx ty) span $ case coref of
    AppTyCF t1 tys -> AppTyCF (go t1) $ applyTyCtx <$> tys
    DropCF var varTy body -> DropCF var (applyTyCtx varTy) $ go body
    LamCF fix polyB argB env t1 -> LamCF fix polyB (fmap applyTyCtx <$> argB) env $ go t1
    _ -> go <$> coref
    where
    applyTyCtx = typeAppSubs tyCtx

-- | Substitute type arguments into the types of arguments.
typeSubInArgs :: [Ty] -> [(SVar, Ty, Mult)] -> [(SVar, Ty, Mult)]
typeSubInArgs subTys args = zip3 vars (applyTypeParams subTys tys) mults where
  (vars, tys, mults) = unzip3 args

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

-- | Specialize a type if it's a data type.
specTy :: Ty -> Spec ()
specTy ty = case parseTyCon ty of
  Nothing -> pure ()
  Just (v, args) -> do
    cdt <- lookupCoreDataType v
    void $ specDataType cdt args

-- | Specializes a data type and registers it under the mangled name.
--
-- Only does so once.
specDataType :: DataType -> [Ty] -> Spec MVar
specDataType dt tyArgs = do
  guardDecl name $ SpecDataType <$> specDt
  where
  name = mangleDataType (getDataTypeName dt) tyArgs
  specDt = case dt of
    -- TODO (?): loop over the member types and specialize them too.
    EnumType name tyParams cases _ -> do
      let cases' = applyTypeParams tyArgs <$> cases
      forM_ cases' $ traverse_ specTy
      pure $ SpecEnum cases'
    StructType con tyParams fields _ -> do
      let args' = applyTypeParams tyArgs fields
      forM_ args' specTy
      pure $ SpecStruct con args'
    BuiltInType enum -> pure $ SpecBuiltIn $ case enum of
      BuiltInI64 -> assert (tyArgs == []) $ SpecI64
      BuiltInString -> assert (tyArgs == []) $ SpecString

-- | Lookup an already specialized data type.
lookupSpecDataType :: MVar -> Spec SpecDataType
lookupSpecDataType v = do
  specDecls <- gets (.specDecls)
  case M.lookup v specDecls of
    Just (SpecDataType dt) -> pure dt
    _ -> throwError $ NoSpecDataType v

-- | Function to call on all function arguments to make sure the specialized versions
-- are generated.
specFunArgs :: [(SVar, Ty, Mult)] -> Spec ()
specFunArgs = traverse_ \(_, ty, _) -> specTy ty

-- | Calculate the tag value for an enum constructor.
tagValueFor :: Var -> M.HashMap T.Text [Ty] -> Integer
tagValueFor Var{name} conMap = case elemIndex name (M.keys conMap) of
  Nothing -> error "should be prevented by type checking"
  Just i -> toInteger i

-- | Generate a function wrapper around a data constructor to
-- allow for partial application.
--
-- NOTE: in the future, I could rewrite this to allow capturing the
-- already provided arguments. But that means calculating a ClosureEnv
-- and a bunch of extra code.
genDataConFun :: MVar -> Var -> DataType -> [Ty] -> Spec MVar
genDataConFun dtVar conVar rawDT tyArgs = do
  let conFunVar = mangleDataConFun dtVar conVar
  guardDecl conFunVar do
    sdt <- lookupSpecDataType dtVar
    let dtName = Var $ getDataTypeName rawDT
        dtSpan = case rawDT of
          StructType _ _ _ s -> s
          EnumType _ _ _ s -> s
          BuiltInType b -> error "temp: neither I64 or string has a constructor"
        argTys = case sdt of
          SpecStruct _ mems -> mems
          SpecEnum m -> case M.lookup conVar.name m of
            Nothing -> error "should be caught by typechecking"
            Just mems -> mems
          SpecBuiltIn _ -> error "temp: neither I64 or string has a constructor"
        mkName i = Var $ "arg" <> T.pack (show i)
        argVars = mkName <$> [0..length argTys]
        mults = Many:repeat Single
        funArgs = zipWith3 (\v ty m -> (SVar v ty.span, ty, m)) argVars argTys mults
        argExprs = zipWith (\v ty -> (SpecIR ty dtSpan $ VarSF v)) argVars argTys
        f :: Ty -> Ty -> Ty
        f base arg = Ty dtSpan $ TyApp base arg
        irRetTy = foldl' f (Ty dtSpan $ TyCon dtName) tyArgs
        conSF = case sdt of
          SpecStruct _ _ -> StructConSF dtVar argExprs
          SpecEnum conMap ->
            let tagVal = tagValueFor conVar conMap
            in EnumConSF tagVal dtVar conVar argExprs
          SpecBuiltIn b -> error "temp: neither I64 or string has a constructor"
        ir = SpecIR irRetTy dtSpan conSF
    pure $ SpecFun (ClosureEnv M.empty) Nothing funArgs ir

-- | Generate the `SpecIR` for a data constructor, specialize the
-- data type involved, and generate a partially applied function if necessary.
specDataCon :: DataType -> Var -> Span -> Ty -> [Ty] -> [SpecIR] -> Spec (SpecF SpecIR)
specDataCon dt conVar conSpan conTy tyArgs args = do
  let requiredArgCount = getDataConArgNum dt conVar
      argCount = length args
  dtMVar <- specDataType dt tyArgs
  case compare argCount requiredArgCount of
    GT -> error "More arguments than constructor takes; should be caught in type checking"
    EQ -> case dt of
      BuiltInType _ -> error "Currently no constructors for built-in types"
      StructType _ _ _ _ -> pure $ StructConSF dtMVar args
      EnumType _ _ conMap _ ->
        let tagVal = tagValueFor conVar conMap
        in pure $ EnumConSF tagVal dtMVar conVar args
    LT -> do
      fvar <- genDataConFun dtMVar conVar dt tyArgs
      let f = SpecIR conTy conSpan $ ClosureSF fvar (ClosureEnv M.empty)
      pure $ AppSF f args

-- | function for specializing the body of functions.
specExpr :: Core -> Spec SpecIR
specExpr core@Core{span, coref} = do
  sp <- mainBody
  let err = error $ "spec type is a lifetime. Spec: " <> show sp <> "\n\nCore: " <> show core.ty
  case sp.ty.tyf of
    LtJoin _ -> err
    LtOf _ -> err
    _ -> pure sp
  where
  mainBody = do
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
      DropCF sv ty t1 -> fmap sf $ DropSF sv ty <$> specExpr t1
      LiteralCF lit -> pure $ sf $ LiteralSF lit
      ConCF dt v -> sf <$> specDataCon dt v span core.ty [] []
      AppTmCF t1 args -> do
        case t1.coref of
          -- Because we want to immediately invoke appropriate constructors
          -- we do this.
          AppTyCF (Core _ conSpan (ConCF dt conVar)) tyArgs -> do
            args' <- traverse specExpr args
            sf <$> specDataCon dt conVar conSpan t1.ty tyArgs args'
          ConCF dt conVar -> do
            args' <- traverse specExpr args
            sf <$> specDataCon dt conVar t1.span t1.ty [] args'
          _ -> do
            t1' <- specExpr t1
            args' <- traverse specExpr args
            pure $ sf $ AppSF t1' args'
      AppTyCF t1 tys -> case t1.coref of
        ConCF dt var -> sf <$> specDataCon dt var span core.ty tys []
          -- mvar <- specDataType dt tys
          -- pure $ sf $ ConSF mvar var
        -- Recursive functions should be picked up here as well.
        LocalVarCF v -> sf <$> specLocalFun v tys
        ModuleVarCF v -> do
          mvar <- specFunDef v tys
          pure $ sf $ ClosureSF mvar $ ClosureEnv M.empty
        LamCF fix polyB argB env body -> throwError $ NoImmediateSpec span
        -- NOTE: how do we handle trying to specialize a reference?
        -- I think that's automatically rejected?
        _ -> error "Can't specialize this? Not certain if this can happen."
      CaseCF t1 branches -> fmap sf $ CaseSF <$>
        specExpr t1 <*> traverse (traverse specExpr) branches
      LetCF sv t1 t2 -> case t1.coref of
        LamCF fix polyB argB env body
          | polyB /= [] -> do
              let argB' = addMultToArgs core.ty argB
                  poly = PolyLambda fix polyB argB' env body
              withPolyLambda sv.var poly $ specExpr t2
        _ -> fmap sf $ LetSF sv <$> specExpr t1 <*> specExpr t2
      LamCF fix [] argB env body -> do
        let argB' = addMultToArgs core.ty argB
        mvar <- storeLambda fix argB' env body
        pure $ sf $ ClosureSF mvar env
      LamCF _ polyB _ _ _ -> error "Should be caught by MustSpec at start"
  sf = SpecIR core.ty core.span

-- | Generate a fresh lambda name using `lambdaCounter`
-- and the types used to specialize it.
freshLambdaName :: [Ty] -> Spec MVar
freshLambdaName tys = do
  ctx <- get
  put $ ctx{lambdaCounter=ctx.lambdaCounter+1}
  pure $ mangleLambda ctx.enclosingFun tys ctx.lambdaCounter

-- | Insert a SpecDecl.
addSpecDecl :: MVar -> SpecDecl -> Spec ()
addSpecDecl mvar sd = modify' \ctx -> ctx
  { specDecls = M.insert mvar sd ctx.specDecls
  , specDeclOrder = (mvar,sd):ctx.specDeclOrder
  }

-- | Store a non-polymorphic lambda in `specDecls`.
storeLambda :: Maybe SVar -> [(SVar, Ty, Mult)] -> ClosureEnv -> Core -> Spec MVar
storeLambda fix args env body = do
  specFunArgs args
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
            argB' = typeSubInArgs tyArgs argB
        specFunArgs argB'
        body <- specExpr bodyCore'
        pure $ SpecFun env fix argB' body
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
  specFunArgs args
  body <- specExpr coreBody
  modify' \ctx -> ctx
    { localFuns = entryLocals
    , enclosingFun = entryEnclosingFun
    }
  pure $ SpecFun (ClosureEnv M.empty) fix args body
  where
  mangledName = mangleFun name tyArgs
  getBody :: Core -> (Maybe SVar, [(SVar, Ty, Mult)], Core)
  getBody fullCore@Core{coref} = case coref of
    LamCF fix polyB argB (ClosureEnv env) body ->
      -- Top level Function definitions should never be able
      -- to capture environment variables.
      assert (env == M.empty) $
      let body' = typeSubInCore tyArgs body
          argB' = addMultToArgs fullCore.ty argB
          args = typeSubInArgs tyArgs argB'
      in assert (length polyB == length tyArgs)
        (fix, args, body')
    _ -> (Nothing, [], fullCore)

-- | Specialize a core module.
--
-- Uses an unspecialized main function as an entry point.
specModule :: M.HashMap Var DataType -> [(Var, Core)] ->
  Either SpecErr ([(MVar, SpecDecl)], M.HashMap MVar SpecDecl)
specModule dataTypes coreFuns = run $ specFunDef (Var "main") []
  where
  ctx = SpecCtx
    { specDecls = M.empty
    , specDeclOrder = []
    , coreDataTypes = dataTypes
    , coreFuns = M.fromList coreFuns
    , localFuns = M.empty
    , lambdaCounter = 0
    , enclosingFun = error "Should be overriden by specFunDef"
    }
  extract SpecCtx{specDeclOrder,specDecls} = (specDeclOrder, specDecls)
  run spec = fmap (extract . snd) $ runExcept $ flip runStateT ctx $ unSpec spec
