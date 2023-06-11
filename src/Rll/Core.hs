{-# LANGUAGE DeriveTraversable #-}
module Rll.Core
  ( CoreF(..), Core(..)
  ) where

import Rll.Ast

import Data.Text (Text)

-- | This IR is produced during type checking and annotates every
-- term with its type.
data CoreF a
  = CaseCF a [(SVar, [SVar], a)]
  | LetStructCF SVar [SVar] a a
  | LetCF SVar a a
  | LamCF SVar Ty a
  | PolyCF TyVarBinding Kind a
  | VarCF Var
  | ConCF Var
  | CopyCF Var
  | RefCF Var
  | DropCF SVar a
  | AppTmCF a a
  | FixCF SVar a
  | AppTyCF a Ty
  | IntLitCF Integer
  | StringLitCF Text
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | This annotates everything in `CoreF` with its type and span.
data Core = Core {ty::Ty, span::Span, core::(CoreF Core)}
  deriving (Eq)

instance Show Core where
  showsPrec p (Core _ _ cf) = showsPrec p cf

instance Spans Core where
  getSpan = (.span)
