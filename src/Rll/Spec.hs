module Rll.Spec
  (
  ) where

import Rll.Ast
import Rll.Context (DataType(..))
import Rll.Core
import Rll.Tc (rawTypeSub)

import Data.HashMap.Strict qualified as M
import Data.IntMap.Strict qualified as IM
import qualified Data.HashSet as S
import Data.Text (Text)
import Data.Text qualified as T
import Control.Monad.State (MonadState(..), StateT, modify', runStateT, gets)
import Control.Monad.Except (MonadError(..), Except, runExcept)
import Data.List (foldl')
import Control.Exception (assert)
import Data.Hashable (Hashable(..))

data ClosureEnv = ClosureEnv
  { moved :: M.HashMap Var Ty
  , referenced :: M.HashMap Var Ty
  }

data SpecDecl
  = SpecFun ClosureEnv [(Var, Ty)] SpecIR
  | Instantiate DataType [Ty]

data SpecF a
  = CaseSF a [(SVar, [SVar], a)]
  | LetStructSF SVar [SVar] a a
  | LetSF SVar a a
  -- | Create an initial closure for a function.
  --
  -- The first hashset is variables that are moved into the closure.
  -- The second is variables that are referenced by it and will have
  -- their references put in the closure.
  | ClosureSF MVar (S.HashSet Var) (S.HashSet Var)
  -- | Local variable.
  | VarSF Var
  -- NOTE maybe have information about the source data type here? I'd
  -- probably add that in when building `Core`.
  | ConSF Var
  | CopySF Var
  -- | Used when a `RefCF` in a lambda refers to an external variable.
  | ExtRefSF Var
  | RefSF Var
  | DropSF SVar a
  | AppSF a a
  | LiteralSF Literal
  deriving (Show, Eq, Functor, Foldable, Traversable)

data SpecIR = SpecIR {ty :: Ty, span :: Span, spec :: (SpecF SpecIR)}

-- | A mangled variable name.
data MVar = MVar Var Text
  deriving (Show, Eq, Ord)

instance Hashable MVar where
  hashWithSalt s (MVar v t) = s `hashWithSalt` v `hashWithSalt` t

mangle :: Var -> [Ty] -> MVar
mangle = undefined

data CoreLambda = CoreLambda ClosureEnv [(Var, Ty)] Core

data SpecCtx = SpecCtx
  { specDecls :: M.HashMap MVar SpecDecl
  , lambdas :: M.HashMap Var CoreLambda
  , lambdaCounter :: Int
  , dataTypes :: M.HashMap Var DataType
  , coreFuns :: M.HashMap Var Core
  }

data SpecErr
  -- | Could not find the function in `coreFuns`.
  = NoCoreFun Var

newtype Spec a = MkSpec { unSpec :: StateT SpecCtx (Except SpecErr) a }
  deriving (Functor, Applicative, Monad, MonadError SpecErr, MonadState SpecCtx)

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
  go xi fullCore@Core{ty, span, core} = Core (goTy ty) span $ case core of
    AppTyCF t1 tys -> AppTyCF (f t1) $ goTy <$> tys
    LamCF fix polyB argB t1 -> LamCF fix polyB (fmap goTy <$> argB) $ f t1
    _ -> f <$> core
    where
    -- Because the type arguments should have no type variables, we
    -- don't need to shift them.
    g ty (i, arg) = rawTypeSub (xi+i) arg ty
    goTy baseTy = foldl' g baseTy $ zip [0..] tyCtx
    f = go xi

{-
-- | Transform a Core such that all type applications are done in one
-- place in a single operation.
condenseAppTy :: Core -> Core
condenseAppTy = go M.empty where
  -- What do you do if you return a polymorphic function from an if
  -- statement and then dynamically apply it?

  -- | We take a map of a variable to a substitution for it.
  -- This holds type applications that have already happened.
  --
  -- If we have a lambda that takes partial type arguments -- which
  -- is an absurd edge case but legal -- then we delete the applications
  -- from there and move them to instead happen where they're finished.
  go :: M.HashMap Var [Ty] -> Core -> Core
  go ctx fullCore@Core{core} = case core of
    LetCF v t1 t2 -> case t1.ty of
      Univ _ _ _ _ _ _ -> case t1.core of
        AppTyCF lam@Core{core=LamCF _ _ _ _} tys ->
          let ctx' = M.insert v $ Core lam.ty lam.span 
          in LetCF v lam $ go (M.insert )
      _ -> go ctx <$> core
    _ -> go ctx <$> core
  -}


-- TODO function for specializing the body of functions
specExpr :: Core -> Spec SpecIR
specExpr fullCore@Core{core} = case core of
  LetCF sv t1 t2 -> sf $ LetSF sv <$> specExpr t1 <*> specExpr t2
  LamCF fix polyB argB body -> undefined
  where sf = fmap $ SpecIR fullCore.ty fullCore.span

-- TODO function for registering a lambda.
-- TODO function for going off and specializing a separate function
-- TODO function for specializing a lambda.
specLambda :: Var -> [Ty] -> Spec Var
specLambda = undefined

specFunDef :: Var -> [Ty] -> Spec ()
specFunDef name tyArgs = do
  -- We save the lambdas we started with, and use a blank map for
  -- when we're specializing this function, since it's separate.
  entryLambdas <- gets (.lambdas)
  modify' \ctx -> ctx{lambdas=M.empty}
  (args, coreBody) <- getBody <$> getCoreFun name
  body <- specExpr coreBody
  let mangledName = mangle name tyArgs
      decl = SpecFun (ClosureEnv M.empty M.empty) args body
  modify' \ctx -> ctx
    { specDecls = M.insert mangledName decl ctx.specDecls
    , lambdas = entryLambdas
    }
  where
  getBody :: Core -> ([(Var, Ty)], Core)
  getBody fullCore@Core{core} = case core of
    LamCF fix polyB argB body ->
      let f (v,ty) = (v.var, ty)
          body' = typeSubInCore tyArgs body
      in assert (length polyB == length tyArgs) (f <$> argB, body')
    _ -> ([], fullCore)

specModule :: M.HashMap Var DataType -> [(Var, Core)] ->
  Either SpecErr (M.HashMap MVar SpecDecl)
specModule dataTypes coreFuns = run $ specFunDef (Var "main") []
  where
  ctx = SpecCtx
    { specDecls = M.empty
    , dataTypes = dataTypes
    , coreFuns = M.fromList coreFuns
    , lambdas = M.empty
    }
  run spec = fmap ((.specDecls) . snd) $ runExcept $ flip runStateT ctx $ unSpec spec
