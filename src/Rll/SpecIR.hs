module Rll.SpecIR
  ( SpecF(..), SpecIR(..), MVar
  , mangleDataType, mangleFun, mangleLambda
  ) where

import Rll.Ast
import Data.Hashable (Hashable(..))
import Rll.Core (ClosureEnv)

import Data.Text (Text)
import Data.Text qualified as T

data SpecF a
  = CaseSF a [CaseBranch a]
  | LetStructSF SVar [SVar] a a
  | LetSF SVar a a
  -- | Create an initial closure for a function.
  --
  -- The first hashset is variables that are moved into the closure.
  -- The second is variables that are referenced by it and will have
  -- their references put in the closure.
  | ClosureSF MVar ClosureEnv
  -- | This is used to indicate that we're re-using the closure
  -- environment for a recursive function call.
  --
  -- The second argument is the name of the variable holding
  -- the recursive function reference and acts as an identifier.
  | RecClosureSF MVar Var
  -- | Local variable.
  | VarSF Var
  -- NOTE maybe have information about the source data type here? I'd
  -- probably add that in when building `Core`.
  -- | A data type constructor. Has the mangled name of the data type
  -- and the name of the constructor.
  | ConSF MVar Var
  | CopySF Var
  | RefSF Var
  | DropSF SVar a
  | AppSF a [a]
  | LiteralSF Literal
  deriving (Show, Eq, Functor, Foldable, Traversable)

data SpecIR = SpecIR {ty :: Ty, span :: Span, specf :: (SpecF SpecIR)}
  deriving (Show, Eq)

-- | A mangled variable name.
data MVar = MVar !Var !Text
  deriving (Show, Eq, Ord)

instance Hashable MVar where
  hashWithSalt s (MVar v t) = s `hashWithSalt` v `hashWithSalt` t

mangleType :: Ty -> Text
mangleType Ty{tyf} = case mangleType <$> tyf of
  TyVar tv -> notConcrete
  Univ _ _ _ _ _ -> notConcrete
  LtOf _ -> notReachLt
  LtJoin _ -> notReachLt
  TyApp a b -> T.concat [a, "(", b, ")"]
  TyCon v -> v.name
  RefTy _ a -> T.concat ["[", a, "]"]
  FunTy _ a _ b -> T.concat ["{", a, "-", b, "}"]
  where
    notReachLt = error "Should never reach a lifetime when mangling"
    notConcrete = error "Cannot mangle a non-concrete type"

mangleTypes :: [Ty] -> Text
mangleTypes tys = T.intercalate "," $ mangleType <$> tys

mangleDataType :: Text -> [Ty] -> MVar
mangleDataType dtName tys = MVar (Var dtName) $ T.cons '*' $ mangleTypes tys

mangleFun :: Var -> [Ty] -> MVar
mangleFun v tys = MVar v $ T.cons '^' $ mangleTypes tys

mangleLambda :: MVar -> [Ty] -> Int -> MVar
mangleLambda (MVar en slug) tys i = mangleFun (Var name) tys
  where
    name = T.concat [en.name, "%", slug, "@", T.pack (show i)]
