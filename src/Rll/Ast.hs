{-# LANGUAGE DuplicateRecordFields, PatternSynonyms, BangPatterns #-}
module Rll.Ast where

import Data.Text (Text)
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T
import Text.Megaparsec (Pos)
import Data.Hashable (Hashable(..))

newtype Var = Var {name::Text}
  deriving (Eq, Ord, Hashable)

instance Show Var where
  show v = T.unpack v.name

{-
instance Hashable Var where
  hashWithSalt s (Var t) = hashWithSalt s t
-}

data TyVar = MkTyVar {name::Text, index::Int}

instance Show TyVar where
  show (MkTyVar name index) = T.unpack name <> "@" <> show index

instance Eq TyVar where
  (MkTyVar _ i) == (MkTyVar _ j) = i == j

newtype TyVarBinding = TyVarBinding {name::Text}
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
  , startLine :: !Int
  , startColumn :: !Int
  , endLine :: !Int
  , endColumn :: !Int
  }
  deriving Show

data SVar = SVar {var::Var, span::Span}

instance Show SVar where
  show v = show v.var

instance Eq SVar where
  v1 == v2 = v1.var == v2.var

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

instance Spans SVar where
  getSpan sv = sv.span

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
  deriving (Eq)

instance Show Ty where
  show (TyVar tv _) = T.unpack tv.name
  show (TyCon v _) = T.unpack v.name
  show (LtOf v _) = "'" <> T.unpack v.name
  show (FunTy m a lts b _) = show a <> " -" <> m' <> show lts <> "> " <> show b
    where m' = case m of
            Many -> "M"
            Single -> "S"
  show (LtJoin tys _) = show tys
  show (RefTy l t _) = "&" <> show l <> " " <> show t
  show (Univ m lts b k t _) = "forall " <> m' <> " " <> show lts <> " "
                              <> show b <> " : " <> show k <> ". " <> show t
    where m' = case m of
            Many -> "M"
            Single -> "S"

instance Spans Ty where
  getSpan ty = case ty of
    TyVar _ s -> s
    TyCon _ s -> s
    LtOf _ s -> s
    FunTy _ _ _ _ s -> s
    LtJoin _ s -> s
    RefTy _ _ s -> s
    Univ _ _ _ _ _ s -> s

data CaseBranch = CaseBranch SVar [SVar] Tm
  deriving (Show, Eq)

data Tm
  = Case Tm [CaseBranch] Span
  | LetStruct SVar [SVar] Tm Tm Span
  | Let SVar Tm Tm Span
  | FunTm SVar (Maybe Ty) Tm Span
  | Poly (Maybe (TyVarBinding, Kind)) Tm Span
  | TmVar Var Span
  | TmCon Var Span
  | Copy Var Span
  | RefTm Var Span
  | AppTy Tm Ty Span
  | Drop SVar Tm Span
  | AppTm Tm Tm Span
  -- | argument var, function var, body
  -- Recursive functions cannot be synthesized.
  | RecFun SVar SVar Tm Span
  | Anno Tm Ty Span
  deriving (Show, Eq)

instance Spans Tm where
  getSpan tm = case tm of
    Case _ _ s -> s
    LetStruct _ _ _ _ s -> s
    Let _ _ _ s -> s
    FunTm _ _ _ s -> s
    Poly _ _ s -> s
    TmVar _ s -> s
    TmCon _ s -> s
    Copy _ s -> s
    RefTm _ s -> s
    AppTy _ _ s -> s
    Drop _ _ s -> s
    AppTm _ _ s -> s
    RecFun _ _ _ s -> s
    Anno _ _ s -> s

