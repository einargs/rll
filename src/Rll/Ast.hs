module Rll.Ast where

import Data.Text (Text)

data Var = Var Text Int
  deriving Eq

data Kind
  = Ty
  | Lifetime
  deriving Eq

data Mult
  = Single
  | Many
  deriving Eq

data Ty
  = UnitTy
  | SumTy Ty Ty
  | ProdTy Ty Ty
  | Static
  | TyVar Var
  | LtOf Var
  -- | function type; Multiplicity, Input, Lifetime, Output
  | FunTy Mult Ty Ty Ty
  | LtJoin [Ty]
  | RefTy Ty Ty
  | Univ Mult Ty Var Kind Ty
  | RecTy Var Ty
  deriving Eq

data Tm
  = Unit
  | LetUnit Tm Tm
  | InL Tm
  | InR Tm
  | Case Mult Tm Var Tm Var Tm
  | ProdTm Tm Tm
  | LetProd Var Var Tm Tm
  | Let Var Tm Tm
  | FunTm Var (Maybe Ty) Tm
  | Poly Mult Var Kind Tm
  | TmVar Var
  | Copy Var
  | RefTm Var
  | AppTy Tm Ty
  | Drop Var Tm
  | AppTm Tm Tm
  | Fold Ty Tm
  | Unfold Tm
  | UnfoldRef Tm
  | RecFun Var Var Var (Maybe Ty) Tm
  | Anno Tm Ty

