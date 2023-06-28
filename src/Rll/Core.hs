{-# LANGUAGE DeriveTraversable #-}
module Rll.Core
  ( CoreF(..), Core(..), ClosureEnv(..), ClosureUse(..)
  , extendAppTm
  ) where

import Rll.Ast
import Rll.Context (DataType)

import Data.Text (Text)
import Prettyprinter
import Data.HashMap.Strict qualified as M
import Data.Aeson (FromJSON(..), ToJSON(..))
import GHC.Generics (Generic)

data ClosureUse a
  = Moved a
  | Refd a
  | Copied a
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (FromJSON, ToJSON)

newtype ClosureEnv = ClosureEnv
  { envMap :: M.HashMap Var (ClosureUse Ty)
  }
  deriving (Eq, Show)

instance FromJSON ClosureEnv where
  parseJSON = fmap (ClosureEnv . M.fromList) . parseJSON

instance ToJSON ClosureEnv where
  toJSON (ClosureEnv m) = toJSON $ M.toList m

instance Pretty ClosureEnv where
  pretty (ClosureEnv m)
    | m == M.empty = "{}"
    | otherwise = "{" <+> align (vsep mems) <+> "}" where
      mems = punctuate "," $ toMem <$> M.toList m
      toMem (v, Moved ty) = "moved" <+> pretty v <+> "=" <+> pretty ty
      toMem (v, Refd ty) = "refd" <+> pretty v <+> "=" <+> pretty ty
      toMem (v, Copied ty) = "copied" <+> pretty v <+> "=" <+> pretty ty

-- | This IR is produced during type checking and annotates every
-- term with its type.
data CoreF a
  = CaseCF a [CaseBranch a]
  | LetStructCF SVar [SVar] a a
  | LetCF SVar a a
  | LamCF (Maybe SVar) [(TyVarBinding, Kind)] [(SVar, Ty)] ClosureEnv a
  | ModuleVarCF Var
  | LocalVarCF Var
  | ConCF DataType Var
  | CopyCF Var
  | RefCF Var
  | DropCF SVar a
  | AppTmCF a [a]
  | AppTyCF a [Ty]
  | LiteralCF Literal
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | This annotates everything in `CoreF` with its type and span.
data Core = Core {ty::Ty, span::Span, coref::(CoreF Core)}
  deriving (Eq)

extendAppTm :: Core -> Core -> CoreF Core
extendAppTm t1@Core{coref} t2 = case coref of
  AppTmCF f args -> AppTmCF f $ args <> [t2]
  _ -> AppTmCF t1 [t2]

instance Show Core where
  showsPrec i (Core _ _ cf) = showsPrec i cf

instance Spans Core where
  getSpan = (.span)
