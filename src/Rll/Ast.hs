{-# LANGUAGE OverloadedRecordDot, DuplicateRecordFields, PatternSynonyms, BangPatterns #-}
module Rll.Ast where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Hashable (Hashable(..))
import Prettyprinter

newtype Var = Var {name::Text}
  deriving (Eq, Ord, Hashable)

instance Show Var where
  show v = T.unpack v.name

instance Pretty Var where
  pretty (Var n) = pretty n

data TyVar = MkTyVar {name::Text, index::Int}

instance Pretty TyVar where
  pretty (MkTyVar name index) = pretty name <> "@" <> pretty index

instance Show TyVar where
  show = show . pretty

instance Eq TyVar where
  (MkTyVar _ i) == (MkTyVar _ j) = i == j

instance Ord TyVar where
  compare (MkTyVar _ i) (MkTyVar _ j) = compare i j

instance Hashable TyVar where
  hashWithSalt s (MkTyVar _ i) = hashWithSalt s i

newtype TyVarBinding = TyVarBinding {name::Text}
  deriving Show

instance Eq TyVarBinding where
  _ == _ = True

instance Ord TyVarBinding where
  compare _ _ = EQ

data EnumCon = EnumCon Text [Ty]
  deriving (Show, Eq)

data TypeParam = TypeParam { name::Text, kind:: Kind }
  deriving (Show, Eq)

data Decl
  = FunDecl Text Ty Tm Span
  | EnumDecl Text [TypeParam] [EnumCon] Span
  | StructDecl Text [TypeParam] [Ty] Span
  deriving (Show, Eq)

data Span = Span
  { file :: FilePath
  , startLine :: !Int
  , startColumn :: !Int
  , endLine :: !Int
  , endColumn :: !Int
  }

instance Show Span where
  show Span{..} = file <> " " <> p startLine startColumn <> "-" <> p endLine endColumn where
    p a b = show a <> ":" <> show b

instance Hashable Span where
  hashWithSalt s _ = hashWithSalt s (0::Int)

data SVar = SVar {var::Var, span::Span}

instance Show SVar where
  show v = show v.var

instance Pretty SVar where
  pretty v = pretty v.var

instance Eq SVar where
  v1 == v2 = v1.var == v2.var

instance Eq Span where
  _ == _ = True

instance Ord Span where
  compare _ _ = EQ

data Kind
  = TyKind
  | LtKind
  | TyOpKind Kind Kind
  deriving (Eq, Show)

-- | Pretty print a kind.
--
-- Boolean controls whether we wrap a type operator kind in parentheses.
basePrettyKind :: Bool -> Kind -> Doc ann
basePrettyKind _ TyKind = "Type"
basePrettyKind _ LtKind = "Lifetime"
basePrettyKind b (TyOpKind t1 t2) = (if b then parens else id) $
  basePrettyKind True t1 <> softline <> "->" <+> basePrettyKind False t2

instance Pretty Kind where
  pretty = basePrettyKind False

data Mult
  = Single
  | Many
  deriving (Eq, Show)

class Spans a where
  getSpan :: a -> Span

instance Spans SVar where
  getSpan sv = sv.span

data Ty
  = TyVar TyVar Span
  | TyCon Var Span
  | LtOf Var Span
  -- | function type; Multiplicity, Input, Lifetime, Output
  | FunTy Mult Ty Ty Ty Span
  -- | Union of lifetimes.
  --
  -- Empty list means static lifetime.
  | LtJoin [Ty] Span
  | RefTy Ty Ty Span
  -- | Multiplicity, lifetimes, type var name, type var kind, body
  | Univ Mult Ty TyVarBinding Kind Ty Span
  -- | Type application to type operators
  | TyApp Ty Ty Span
  deriving (Eq)

-- | Indicates when we need to add parentheses when pretty printing a type.
data TyParenLevel
  = NoTyParen
  -- ^ Do not add parentheses.
  | TyFunParen
  -- ^ Add parentheses if we're rendering a function type.
  | TyAppParen
  -- ^ Add parentheses if we're rendering a type application or a function type.
  deriving (Eq, Ord)

-- | Pretty prints types.
basePrettyTy :: TyParenLevel -> Ty -> Doc ann
basePrettyTy parenLevel ty = case ty of
  TyVar tv _ -> pretty tv
  TyCon v _ -> pretty v
  LtOf v _ -> "'" <> pretty v
  FunTy m a lts b _ -> parenFor TyFunParen $
    basePrettyTy TyFunParen a <> layer (mconcat
    [ "-", prettyM m
    , basePrettyTy NoTyParen lts
    , ">" <+> basePrettyTy NoTyParen b
    ])
  LtJoin tys _ -> list $ basePrettyTy NoTyParen <$> tys
  RefTy l t _ -> "&" <> basePrettyTy TyAppParen l <+> basePrettyTy TyAppParen t
  Univ m lts b k t _ -> parenFor TyFunParen $ "forall"
    <+> prettyM m <+> basePrettyTy TyAppParen lts
    <+> pretty b.name <> ":" <+> pretty k <> "."
    <> layer (basePrettyTy NoTyParen t)
  TyApp a b _ -> parenFor TyAppParen $ pretty a <+> pretty b
  where
    layer doc = softline <> nest 2 doc
    prettyM m = case m of
      Many -> "M"
      Single -> "S"
    parenFor lvl | lvl <= parenLevel = parens
                 | otherwise = id

instance Pretty Ty where
  pretty = basePrettyTy NoTyParen

instance Show Ty where
  show = show . pretty

{-
instance Show Ty where
  show (TyVar tv _) = show tv
  show (TyCon v _) = T.unpack v.name
  show (LtOf v _) = "'" <> T.unpack v.name
  show (FunTy m a lts b _) = show a <> " -" <> m' <> show lts <> "> " <> show b
    where m' = case m of
            Many -> "M"
            Single -> "S"
  show (LtJoin tys _) = show tys
  show (RefTy l t _) = "&" <> show l <> " " <> show t
  show (Univ m lts b k t _) = "forall " <> m' <> " " <> show lts <> " "
                              <> T.unpack b.name <> " : " <> show k <> ". " <> show t
    where m' = case m of
            Many -> "M"
            Single -> "S"
  show (TyApp t1 t2 _) = "(" <> show t1 <> ") " <> " (" <> show t2 <> ")"
-}

instance Spans Ty where
  getSpan ty = case ty of
    TyVar _ s -> s
    TyCon _ s -> s
    LtOf _ s -> s
    FunTy _ _ _ _ s -> s
    LtJoin _ s -> s
    RefTy _ _ s -> s
    Univ _ _ _ _ _ s -> s
    TyApp _ _ s -> s

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
  -- | function name var, body
  --
  -- Cannot be synthesized.
  | FixTm SVar Tm Span
  | Anno Tm Ty Span
  | IntLit Integer Span
  | StringLit Text Span
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
    FixTm _ _ s -> s
    Anno _ _ s -> s
    IntLit _ s -> s
    StringLit _ s -> s

