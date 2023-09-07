{-# LANGUAGE PatternSynonyms #-}

module Rll.Ast
  ( Span(..), Spans(..)
  , Var(..), TyVar(..), SVar(..), TyVarBinding(..)
  , EnumCon(..), TypeParam(..), Decl(..)
  , Kind(..), Mult(..), Ty(..), TyF(.., I64Ty, StringTy)
  , Tm(..), TmF(..), CaseBranch(..), Literal(..)
  , CaseBranchTy(..)
  , parseTyCon, parseFunTy
  , ClosureUse(..), ClosureEnv(..)
  , i64TyName, stringTyName
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict qualified as M
import Prettyprinter
import Data.Aeson (FromJSON, ToJSON, parseJSON, toJSON)
import Data.Aeson qualified as A
import Data.Aeson.Types qualified as AT
import GHC.Generics (Generic)
import Data.Vector qualified as V

newtype Var = Var {name::Text}
  deriving (Eq, Ord)
  deriving newtype (Hashable, FromJSON, ToJSON)

instance Show Var where
  show v = T.unpack v.name

instance Pretty Var where
  pretty (Var n) = pretty n

data TyVar = MkTyVar {name::Text, index::Int}
  deriving (Generic, FromJSON, ToJSON)

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
  deriving (Generic)
  deriving anyclass (FromJSON, ToJSON)

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

-- TODO: custom from and to json stuff that just uses an array.
instance FromJSON Span where
  parseJSON = A.withArray "Span" \arr ->
    let idx :: FromJSON a => Int -> AT.Parser a
        idx i = case arr V.!? i of
          Just v -> A.parseJSON v
          Nothing -> fail $ "Expected value at index " <> show i
    in Span <$> idx 0 <*> idx 1 <*> idx 2 <*> idx 3 <*> idx 4

instance ToJSON Span where
  toJSON (Span file sl sc el ec) =
    A.Array $ V.fromList $ [A.toJSON file] <> fmap A.toJSON [sl, sc, el, ec]

instance Show Span where
  show Span{..} = file <> " " <> p startLine startColumn <> "-" <> p endLine endColumn where
    p a b = show a <> ":" <> show b

instance Hashable Span where
  hashWithSalt s _ = hashWithSalt s (0::Int)

data SVar = SVar {var::Var, span::Span}
  deriving (Generic)
  deriving anyclass (FromJSON, ToJSON)

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
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

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
  deriving (Eq, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

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
  deriving (Eq, Functor, Foldable, Traversable, Generic)

instance FromJSON a => FromJSON (TyF a) where
  parseJSON = A.genericParseJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}

instance ToJSON a => ToJSON (TyF a) where
  toJSON = A.genericToJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}
  toEncoding = A.genericToEncoding A.defaultOptions{A.sumEncoding=A.TwoElemArray}

data Ty = Ty { span :: Span, tyf :: (TyF Ty) }
  deriving (Eq)

i64TyName :: Var
i64TyName = Var "I64"

pattern I64Ty :: TyF a
pattern I64Ty = TyCon (Var "I64")

stringTyName :: Var
stringTyName = Var "String"

pattern StringTy :: TyF a
pattern StringTy = TyCon (Var "String")

instance FromJSON Ty where
  parseJSON v = Ty es <$> parseJSON v
    where es = Span "" 1 1 1 1

instance ToJSON Ty where
  toJSON Ty{tyf} = toJSON tyf

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

-- | If the type is a type constructor followed by type applications,
-- return that; otherwise return nothing.
parseTyCon :: Ty -> Maybe (Var, [Ty])
parseTyCon ty = collectApps [] ty where
  collectApps :: [Ty] -> Ty -> Maybe (Var, [Ty])
  collectApps rs ty = case ty.tyf of
    TyApp b a -> collectApps (a:rs) b
    TyCon v -> Just (v, rs)
    _ -> Nothing

-- | Get the function arguments and return type if this is a function.
--
-- Returns nothing if the function is polymorphic.
parseFunTy :: Ty -> Maybe ([Ty], Ty)
parseFunTy Ty{tyf=FunTy _ arg _ ret} = case parseFunTy ret of
  Nothing -> Just ([arg], ret)
  Just (args, retTy) -> Just (arg:args, retTy)
parseFunTy _ = Nothing

instance Pretty Ty where
  pretty = basePrettyTy NoTyParen

instance Show Ty where
  show = show . pretty

instance Spans Ty where
  getSpan = (.span)

data CaseBranch a = CaseBranch SVar [SVar] a
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (FromJSON, ToJSON)

data CaseBranchTy a = CaseBranchTy SVar [(SVar, Ty)] a
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Literal
  = IntLit Integer
  | StringLit Text
  deriving (Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Show Literal where
  show (IntLit i) = show i
  show (StringLit txt) = show txt

-- | Internal structure of a term.
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

-- | Common elements of a term.
data Tm = Tm {span :: Span, tmf :: TmF Tm }
  deriving (Eq)

instance Show Tm where
  showsPrec i (Tm _ tf) = showsPrec i tf

instance Spans Tm where
  getSpan = (.span)

-- | A marker type for how free variables in a closure
-- are used.
data ClosureUse a
  = Moved a
  | Refd a
  | Copied a
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- | The free variables mentioned inside a closure.
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
