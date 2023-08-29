{-# LANGUAGE DeriveTraversable #-}
module Rll.Core
  ( CoreF(..), Core(..)
  , extendAppTm
  ) where

import Rll.Ast
import Rll.Context (DataType)

-- | This IR is produced during type checking and annotates every
-- term with its type.
data CoreF a
  = CaseCF a [CaseBranchTy a]
  | LetStructCF SVar [(SVar, Ty)] a a
  | LetCF SVar a a
  | LamCF (Maybe SVar) [(TyVarBinding, Kind)] [(SVar, Ty)] ClosureEnv a
  | ModuleVarCF Var
  | LocalVarCF Var
  | ConCF DataType Var
  | CopyCF Var
  | RefCF Var
  | DropCF SVar Ty a
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
