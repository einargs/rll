{-# LANGUAGE DuplicateRecordFields, PatternSynonyms, BangPatterns #-}
module Rll.Ast where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec (Pos)

newtype Var = Var {name::Text}
  deriving (Show, Eq)

data TyVar = MkTyVar {name::Text, index::Int}

instance Show TyVar where
  show (MkTyVar name index) = T.unpack name <> "@" <> show index

instance Eq TyVar where
  (MkTyVar _ i) == (MkTyVar _ j) = i == j

newtype TyVarBinding = TyVarBinding Text
  deriving Show

instance Eq TyVarBinding where
  _ == _ = True

data EnumCon = EnumCon Text [Ty]
  deriving (Show, Eq)

data Decl
  = FunDecl Text Ty Tm Span
  | EnumDecl Text [EnumCon] Span
  | StructDecl Text [Ty] Span
  deriving (Show, Eq)

data Span = Span
  { file :: FilePath
  , startLine :: !Pos
  , startColumn :: !Pos
  , endLine :: !Pos
  , endColumn :: !Pos
  }
  deriving Show

instance Eq Span where
  _ == _ = True

data Kind
  = TyKind
  | LtKind
  deriving (Eq, Show)

data Mult
  = Single
  | Many
  deriving (Eq, Show)

class Spans a where
  getSpan :: a -> Span

-- TODO Write Static as a pattern for LtJoin []
data Ty
  = TyVar TyVar Span
  -- can probably be replaced with `LtJoin []`
  --  | Static
  | TyCon Var Span
  | LtOf Var Span
  -- | function type; Multiplicity, Input, Lifetime, Output
  | FunTy Mult Ty Ty Ty Span
  | LtJoin [Ty] Span
  | RefTy Ty Ty Span
  -- | Multiplicity, lifetimes, type var name, type var kind, body
  | Univ Mult Ty TyVarBinding Kind Ty Span
  deriving (Show, Eq)

instance Spans Ty where
  getSpan ty = case ty of
    TyVar _ s -> s
    LtOf _ s -> s
    FunTy _ _ _ _ s -> s
    LtJoin _ s -> s
    RefTy _ _ s -> s
    Univ _ _ _ _ _ s -> s

data CaseBranch = CaseBranch Var [Var] Tm
  deriving (Show, Eq)

data Tm
  = Case Tm [CaseBranch] Span
  | LetStruct Var [Var] Tm Tm Span
  | Let Var Tm Tm Span
  | FunTm Var (Maybe Ty) Tm Span
  | Poly TyVarBinding Kind Tm Span
  | TmVar Var Span
  | TmCon Var Span
  | Copy Var Span
  | RefTm Var Span
  | AppTy Tm Ty Span
  | Drop Var Tm Span
  | AppTm Tm Tm Span
  -- | argument var, function lifetime var, function var, body
  -- Recursive functions cannot be synthesized.
  | RecFun Var Var Var Tm Span
  | Anno Tm Ty Span
  deriving (Show, Eq)

instance Spans Tm where
  getSpan tm = case tm of
    Case _ _ s -> s
    LetStruct _ _ _ _ s -> s
    Let _ _ _ s -> s
    FunTm _ _ _ s -> s
    Poly _ _ _ s -> s
    TmVar _ s -> s
    Copy _ s -> s
    RefTm _ s -> s
    AppTy _ _ s -> s
    Drop _ _ s -> s
    AppTm _ _ s -> s
    RecFun _ _ _ _ s -> s
    Anno _ _ s -> s

