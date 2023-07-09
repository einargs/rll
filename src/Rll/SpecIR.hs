module Rll.SpecIR
  ( SpecF(..), SpecIR(..), MVar
  , mangleDataType, mangleFun, mangleLambda
  , mangleDataCon, mangleDataConFun, mangleFastFun
  , mangleEntryFun
  , mvarToText
  , SpecDataType(..)
  , SpecBuiltIn(..)
  , SpecDecl(..)
  ) where

import Rll.Ast

import Data.Hashable (Hashable(..))
import Data.HashMap.Strict qualified as M
import Prettyprinter
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector qualified as V
import Data.Aeson (FromJSON, ToJSON, ToJSONKey)
import Data.Aeson qualified as A
import Data.Aeson.Types qualified as AT
import GHC.Generics

data SpecF a
  = CaseSF a [CaseBranch a]
  | LetStructSF SVar [SVar] a a
  | LetSF SVar a a
  -- | Create an initial closure for a function.
  --
  -- The first hashset is variables that are moved into the closure.
  -- The second is variables that are referenced by it and will have
  -- their references put in the closure.
  | ClosureSF MVar ClosureEnv
  -- | This is used to indicate that we're re-using the closure
  -- environment for a recursive function call.
  --
  -- The second argument is the name of the variable holding
  -- the recursive function reference and acts as an identifier.
  --
  -- For now we're not going to specifically optimize this
  -- especially because of the situation where we'd need to
  -- pass the context through other contexts, so we'll just
  -- build a normal partially applied function value at the
  -- start of a recursive function.
  | RecClosureSF MVar Var
  -- | Local variable.
  | VarSF Var
  -- NOTE maybe have information about the source data type here? I'd
  -- probably add that in when building `Core`.
  -- | A data type constructor. Has the mangled name of the data type,
  -- the name of the constructor, and the fully saturated arguments.
  | ConSF MVar Var [a]
  | CopySF Var
  | RefSF Var
  | DropSF SVar Ty a
  | AppSF a [a]
  | LiteralSF Literal
  deriving (Show, Eq, Functor, Foldable, Traversable, Generic)

instance FromJSON a => FromJSON (SpecF a) where
  parseJSON = A.genericParseJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}

instance ToJSON a => ToJSON (SpecF a) where
  toJSON = A.genericToJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}
  toEncoding = A.genericToEncoding A.defaultOptions{A.sumEncoding=A.TwoElemArray}

data SpecIR = SpecIR {ty :: Ty, span :: Span, specf :: (SpecF SpecIR)}
  deriving (Show, Eq)

instance ToJSON SpecIR where
  toJSON SpecIR{ty, specf} = A.toJSON $ [A.toJSON ty, A.toJSON specf]

instance FromJSON SpecIR where
  parseJSON = A.withArray "SpecIR" \arr ->
    let idx :: FromJSON a => Int -> AT.Parser a
        idx i = case arr V.!? i of
          Just v -> A.parseJSON v
          Nothing -> fail $ "Expected value at index " <> show i
        es = Span "" 1 1 1 1
    in do
      i0 <- idx 0
      i1 <- idx 1
      pure $ SpecIR i0 es i1

instance Pretty SpecIR where
  pretty ir = go 0 ir where
    go parenLevel ir@SpecIR{specf} = case specf of
      CaseSF t1 brs ->
        let brDoc (CaseBranch con mems tb) = group $ "|" <+> hsep (pretty <$> (con:mems))
              <+> "->" <> softline <> nest 2 (group $ go 0 tb)
            ofDoc = group $ "case" <+> group (go 0 t1) <+> "of"
        in parenFor 1 $ align $ vsep $ ofDoc:(brDoc <$> brs)
      LetStructSF con mems t1 t2 ->
        "let" <+> group (hsep (pretty <$> (con:mems))) <+> "="
        <+> go 0 t1 <+> "in" <> line <> go 0 t2
      LetSF v t1 t2 ->
        "let" <+> pretty v <+> "="
        <+> group (go 0 t1) <+> "in" <> line <> go 0 t2
      DropSF v _ t1 -> "drop" <+> pretty v <+> "in" <> line <> go 0 t1
      ClosureSF v env -> pretty v <> group (pretty env)
      RecClosureSF mv recFun -> pretty mv <> "{" <> pretty recFun <> "}"
      VarSF v -> "!" <> pretty v
      ConSF dtName con args -> group $ prettyArgs
        (pretty dtName <> "." <> pretty con) args
      CopySF v -> parenFor 1 $ "copy" <+> pretty v
      RefSF v -> "&" <> pretty v
      AppSF t1 ts -> group $ prettyArgs (pretty t1) ts
      LiteralSF lit -> case lit of
        IntLit int -> pretty int
        StringLit txt -> "\"" <> pretty txt <> "\""
      where
      prettyArgs d1 [] = d1
      prettyArgs d1 ts = parenFor 1 $ nest 2 $ sep $ d1:(go 1 <$> ts)
      parenFor threshold
        | parenLevel >= threshold = parens
        | otherwise = id

-- | Eventually we will need this to hold things like the type argument
-- to a `Box`.
data SpecBuiltIn
  = SpecI64
  | SpecString
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty SpecBuiltIn where
  pretty b = case b of
    SpecI64 -> "I64"
    SpecString -> "String"

-- | A specialized data type with fully concrete types.
--
-- We remove the enum name since now we've mangled it.
data SpecDataType
  = SpecEnum (M.HashMap Text [Ty])
  | SpecStruct Text [Ty]
  -- | We do a translation stage to include any type arguments to
  -- things like `Box`.
  | SpecBuiltIn SpecBuiltIn
  deriving (Show, Eq, Generic)
  deriving anyclass (FromJSON, ToJSON)

instance Pretty SpecDataType where
  pretty dt = case dt of
    SpecBuiltIn s -> "=" <+> pretty s <> ";"
    SpecStruct con tys -> "= struct" <+> pretty con <+> braces (nest 2 $ hsep $ pretty <$> tys)
    SpecEnum m -> (softline' <>) $ nest 2 $ align $ "=" <+> case M.toList m of
      (b1:bs) ->
        let f (con, tys) = pretty con <+> nest 2 (hsep $ pretty <$> tys)
        in vsep $ (f b1):((("|" <+>) . f) <$> bs)
      [] -> ";"

-- | A declaration that has been specialized to have fully concrete types
-- with no type variables in them.
--
-- By making both globals and lambdas become the same thing, we make it easy
-- to catch lambdas that need no context in the same transform we catch
-- globals when eventually creating their actual invocable types.
data SpecDecl
  = SpecFun ClosureEnv (Maybe SVar) [(SVar, Ty, Mult)] SpecIR
  | SpecDataType SpecDataType
  deriving (Show, Eq, Generic)

instance FromJSON SpecDecl where
  parseJSON = A.genericParseJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}

instance ToJSON SpecDecl where
  toJSON = A.genericToJSON A.defaultOptions{A.sumEncoding=A.TwoElemArray}
  toEncoding = A.genericToEncoding A.defaultOptions{A.sumEncoding=A.TwoElemArray}

instance Pretty SpecDecl where
  pretty (SpecFun env fix args body) =
    pretty env <> pfix <+> pargs <+> "=" <+> nest 2 (pretty body) where
    pfix = case fix of
      Just v -> " " <> parens ("fix" <+> pretty v)
      Nothing -> mempty
    pargs = fillSep $ parg <$> args
    parg (v, ty, _) = parens $ pretty v <+> ":" <+> pretty ty
  pretty (SpecDataType dt) = pretty dt

-- | A mangled variable name.
data MVar = MVar !Var !Text
  deriving (Eq, Generic)
  deriving anyclass (FromJSON, ToJSON, ToJSONKey)

instance Pretty MVar where
  pretty (MVar v txt) = pretty v <> "%" <> pretty txt

instance Show MVar where
  show = show . pretty

instance Hashable MVar where
  hashWithSalt s (MVar v t) = s `hashWithSalt` v `hashWithSalt` t

mvarToText :: MVar -> Text
mvarToText (MVar v slug) = T.concat [v.name, "%", slug]

mangleType :: Ty -> Text
mangleType Ty{tyf} = case mangleType <$> tyf of
  TyVar tv -> notConcrete
  Univ _ _ _ _ _ -> notConcrete
  LtOf _ -> notReachLt
  LtJoin _ -> notReachLt
  TyApp a b -> T.concat [a, "(", b, ")"]
  TyCon v -> v.name
  RefTy _ a -> T.concat ["[", a, "]"]
  FunTy _ a _ b -> T.concat ["{", a, "-", b, "}"]
  where
    notReachLt = error "Should never reach a lifetime when mangling"
    notConcrete = error "Cannot mangle a non-concrete type"

mangleTypes :: [Ty] -> Text
mangleTypes tys = T.intercalate "," $ mangleType <$> tys

mangleDataType :: Text -> [Ty] -> MVar
mangleDataType dtName tys = MVar (Var dtName) $ mangleTypes tys

mangleDataCon :: MVar -> Var -> MVar
mangleDataCon (MVar (Var dtName) slug) (Var con) = MVar name slug
  where name = Var $ T.concat [dtName, ".", con]

mangleDataConFun :: MVar -> Var -> MVar
mangleDataConFun (MVar (Var dtName) slug) (Var con) = MVar name slug
  where name = Var $ T.concat ["c", dtName, ".", con]

mangleFun :: Var -> [Ty] -> MVar
mangleFun v tys = MVar v $ mangleTypes tys

-- | Utility for creating mangled versions of functions.
mangleFunVer :: Text -> MVar -> MVar
mangleFunVer ver (MVar name slug) = MVar name $ T.concat [slug, ".", ver]

-- | This is the fast version of the function.
mangleFastFun :: MVar -> MVar
mangleFastFun = mangleFunVer "fast"

-- | This is the entry function.
mangleEntryFun :: MVar -> MVar
mangleEntryFun = mangleFunVer "entry"

mangleLambda :: MVar -> [Ty] -> Int -> MVar
mangleLambda (MVar en slug) tys i = mangleFun (Var name) tys
  where
    name = T.concat [en.name, "%", slug, "@", T.pack (show i)]
