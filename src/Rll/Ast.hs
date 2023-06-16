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

instance Show TyVarBinding where
  show b = show b.name

instance Eq TyVarBinding where
  _ == _ = True

instance Ord TyVarBinding where
  compare _ _ = EQ

data EnumCon = EnumCon Text [Ty]
  deriving (Show, Eq)

data TypeParam = TypeParam { name::Text, kind:: Kind }
  deriving (Eq)

instance Show TypeParam where
  showsPrec i (TypeParam n k) = shows n . (" : " <>) . shows k

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

data TyF a
  = TyVar TyVar
  | TyCon Var
  | LtOf Var
  -- | function type; Multiplicity, Input, Lifetime, Output
  | FunTy Mult a a a
  -- | Union of lifetimes.
  --
  -- Empty list means static lifetime.
  | LtJoin [a]
  | RefTy a a
  -- | Multiplicity, lifetimes, type var name, type var kind, body
  | Univ Mult a TyVarBinding Kind a
  -- | Type application to type operators
  | TyApp a a
  deriving (Eq, Functor, Foldable, Traversable)

data Ty = Ty { span :: Span, tyf :: (TyF Ty) }
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
basePrettyTy parenLevel ty@Ty{tyf} = case tyf of
  TyVar tv -> pretty tv
  TyCon v -> pretty v
  LtOf v -> "'" <> pretty v
  FunTy m a lts b -> parenFor TyFunParen $
    basePrettyTy TyFunParen a <> layer (mconcat
    [ "-", prettyM m
    , basePrettyTy NoTyParen lts
    , ">" <+> basePrettyTy NoTyParen b
    ])
  LtJoin tys -> list $ basePrettyTy NoTyParen <$> tys
  RefTy l t -> "&" <> basePrettyTy TyAppParen l <+> basePrettyTy TyAppParen t
  Univ m lts b k t -> parenFor TyFunParen $ "forall"
    <+> prettyM m <+> basePrettyTy TyAppParen lts
    <+> pretty b.name <> ":" <+> pretty k <> "."
    <> layer (basePrettyTy NoTyParen t)
  TyApp a b -> parenFor TyAppParen $
    basePrettyTy TyAppParen a <+> basePrettyTy TyAppParen b
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

instance Spans Ty where
  getSpan = (.span)

data CaseBranch a = CaseBranch SVar [SVar] a
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Literal
  = IntLit Integer
  | StringLit Text
  deriving (Eq)

instance Show Literal where
  show (IntLit i) = show i
  show (StringLit txt) = show txt

data TmF a
  = Case a [CaseBranch a]
  | LetStruct SVar [SVar] a a
  | Let SVar a a
  | FunTm (Maybe SVar) [(TyVarBinding, Kind)] [(SVar, Maybe Ty)] a
  | TmVar Var
  | TmCon Var
  | Copy Var
  | RefTm Var
  | AppTy a [Ty]
  | Drop SVar a
  | AppTm a a
  | Anno a Ty
  | LiteralTm Literal
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Tm = Tm {span :: Span, tmf :: TmF Tm }
  deriving (Eq)

instance Show Tm where
  showsPrec i (Tm _ tf) = showsPrec i tf

instance Spans Tm where
  getSpan = (.span)

