{-# LANGUAGE DuplicateRecordFields #-}
module Rll.Ast where

import Data.Text (Text)

data Var = Var {name::Text, index::Int}
  deriving Show

instance Eq Var where
  (Var _ i) == (Var _ j) = i == j

data Kind
  = TyKind
  | LtKind
  deriving (Eq, Show)

data Mult
  = Single
  | Many
  deriving (Eq, Show)

-- TODO Write Static as a pattern for LtJoin []
data Ty
  = UnitTy
  | SumTy Ty Ty
  | ProdTy Ty Ty
  -- can probably be replaced with `LtJoin []`
  --  | Static
  | TyVar Var
  | LtOf Var
  -- | function type; Multiplicity, Input, Lifetime, Output
  | FunTy Mult Ty Ty Ty
  | LtJoin [Ty]
  | RefTy Ty Ty
  -- | Multiplicity, lifetimes, type var name, type var kind, body
  | Univ Mult Ty Var Kind Ty
  | RecTy Var Ty
  deriving (Show, Eq)

data Tm
  = Unit
  | LetUnit Tm Tm
  | InL Tm
  | InR Tm
  | Case Mult Tm Var Tm Var Tm
  | ProdTm Tm Tm
  | LetProd Mult Var Var Tm Tm
  | Let Var Tm Tm
  | FunTm Var (Maybe Ty) Tm
  | Poly Var Kind Tm
  | TmVar Var
  | Copy Var
  | RefTm Var
  | AppTy Tm Ty
  | Drop Var Tm
  | AppTm Tm Tm
  | Fold Ty Tm
  | Unfold Tm
  -- | argument var, function lifetime var, function var, body
  -- Recursive functions cannot be synthesized.
  | RecFun Var Var Var Tm
  | Anno Tm Ty
  deriving Show

