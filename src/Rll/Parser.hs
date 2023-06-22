{-# LANGUAGE FunctionalDependencies, FlexibleInstances #-}
module Rll.Parser (
  Parser, decl, fileDecls, tm, ty, RllParseError(..),
) where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Functor (($>))
import Control.Monad (void)
import Data.List (foldl')
import Data.Maybe (isJust)
import Data.Char qualified as Char
-- import Text.Megaparsec.Debug

import Rll.Ast

data RllParseError
  = VarIsKeyword Text
  deriving (Show, Eq, Ord)

instance ShowErrorComponent RllParseError where
  showErrorComponent (VarIsKeyword txt) = T.unpack txt <> " is a keyword and cannot be a variable."

type Parser = Parsec RllParseError Text

spanBetween :: SourcePos -> SourcePos -> Span
spanBetween (SourcePos filePath sl sc) (SourcePos _ el ec) =
  Span filePath (unPos sl) (unPos sc) (unPos el) (unPos ec)

spanTo :: Spans a => SourcePos -> a -> Span
spanTo (SourcePos _ sl sc) sp = (getSpan sp) {startLine = unPos sl, startColumn = unPos sc}

spanFrom :: Spans a => a -> SourcePos -> Span
spanFrom sp (SourcePos _ el ec) = (getSpan sp) {endLine=unPos el, endColumn = unPos ec}

spanFromTo :: (Spans a, Spans b) => a -> b -> Span
spanFromTo start end = f (getSpan start) (getSpan end) where
  f s Span{..} = s{endLine=endLine, endColumn=endColumn}

class FromTo a b where
  fromTo :: a -> b -> Span

instance {-# OVERLAPPING #-} FromTo SourcePos SourcePos where
  fromTo = spanBetween

instance (Spans a) => FromTo SourcePos a where
  fromTo = spanTo

instance (Spans a) => FromTo a SourcePos where
  fromTo = spanFrom

instance {-# OVERLAPPABLE #-} (Spans a, Spans b) => FromTo a b where
  fromTo = spanFromTo

class NeedSpan w f | w -> f where
  provideSpan :: Span -> f w -> w

instance NeedSpan Ty TyF where
  provideSpan = Ty

instance NeedSpan Tm TmF where
  provideSpan = Tm

wrap :: (NeedSpan w f, FromTo a b) => a -> b -> f w -> w
wrap a b = provideSpan (a `fromTo` b)

lineComment = L.skipLineComment "//"
blockComment = L.skipBlockCommentNested "/*" "*/"

space :: Parser ()
space = L.space C.space1 lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

validateForKeywords :: Parser Text -> Parser Text
validateForKeywords m = do
  sp <- getSourcePos
  txt <- m
  if txt `elem` keywords
    then customFailure $ VarIsKeyword txt
    else pure $ txt

mkVarParser :: Parser Char -> Parser Text
mkVarParser m = validateForKeywords $ T.cons <$> m <*> takeWhileP Nothing Char.isAlphaNum

rawUpperText :: Parser Text
rawUpperText = mkVarParser C.upperChar

rawLowerText :: Parser Text
rawLowerText = mkVarParser C.lowerChar

upperText :: Parser Text
upperText = lexeme rawUpperText

lowerText :: Parser Text
lowerText = lexeme rawLowerText

upperVar = label "Uppercase variable" $ Var <$> upperText
lowerVar = label "Lowercase variable" $ Var <$> lowerText

mkSVarParser :: Parser Text -> Parser SVar
mkSVarParser m = lexeme do
  s1 <- getSourcePos
  t <- m
  s2 <- getSourcePos
  pure $ SVar (Var t) $ spanBetween s1 s2

upperSVar = label "Uppercase variable" $ mkSVarParser rawUpperText
lowerSVar = label "Lowercase variable" $ mkSVarParser rawLowerText

varPredUtil :: (NeedSpan w f) => Parser () -> (Var -> f w) -> Parser w
varPredUtil pred f = lexeme do
  s1 <- getSourcePos
  pred
  txt <- rawLowerText
  s2 <- getSourcePos
  pure $ wrap s1 s2 $ f (Var txt)

keyword :: Text -> Parser ()
keyword txt = void $ L.symbol space txt

unitw = keyword "()"
letw = keyword "let"
equalw = keyword "="
inw = keyword "in"
casew = keyword "case"
ofw = keyword "of"
barw = keyword "|"
arroww = keyword "->"
colonw = keyword ":"
funw = keyword "\\"
copyw = keyword "copy"
refw = keyword "&"
dropw = keyword "drop"
commaw = keyword ","
enumw = keyword "enum"
structw = keyword "struct"
forallw = keyword "forall"
dotw = keyword "."
semicolonw = keyword ";"
recw = keyword "rec"

keywords :: [Text]
keywords = ["let", "in", "case", "copy", "drop", "rec", "enum", "forall", "struct", "of"]

mkParens :: Parser a -> Parser a
mkParens = between (keyword "(") (keyword ")")

kindp :: Parser Kind
kindp = label "kind" do
  k1 <- subKind
  tyOpContinue k1 <|> pure k1
  where
    subKind = choice [tyKind, ltKind, parenKind]
    parenKind = label "kind level parentheses" $ mkParens kindp
    tyKind = label "type kind" $ keyword "Type" $> TyKind
    ltKind = label "lifetime kind" $ keyword "Lifetime" $> LtKind
    tyOpContinue k1 = label "type operator kind" do
      arroww
      k2 <- kindp
      pure $ TyOpKind k1 k2

mult :: Parser Mult
mult = C.char 'S' $> Single <|> C.char 'M' $> Many

branch :: Show a => String -> Parser a -> Parser a
branch name = try . label name

ty :: Parser Ty
ty = label "type" do
  t1 <- subTy
  funTy t1 <|> pure t1
  where
    subTy = do
      t1 <- simpleTy
      tyApp t1 <|> pure t1
    funTy t1 = branch "function arrow" do
      C.char '-'
      m <- mult
      space
      lts <- ltJoin
      C.char '>'
      space
      t2 <- ty
      pure $ wrap t1 t2 $ FunTy m t1 lts t2
    tyApp t1 = branch "type operator arguments" do
      args <- some simpleTy
      let f t1 t2 = wrap t1 t2 $ TyApp t1 t2
      pure $ foldl' f t1 args

ltJoin :: Parser Ty
ltJoin = branch "lifetime join" do
  s1 <- getSourcePos
  C.char '['
  space
  ltParts <- ty `sepBy` commaw
  C.char ']'
  s2 <- getSourcePos
  space
  pure $ wrap s1 s2 $ LtJoin ltParts

-- | A type that cannot be a type application or type function unless those are
-- in parentheses.
simpleTy :: Parser Ty
simpleTy = choice [univTy, tyVar, tyCon, ltOf, ltJoin, refTy, parenTy] where
    parenTy = label "type level parentheses" $ mkParens ty
    tyVar = branch "type variable" do
      s1 <- getSourcePos
      name <- rawLowerText
      s2 <- getSourcePos
      space
      pure $ wrap s1 s2 $ TyVar (MkTyVar name 0)
    tyCon = branch "type constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ wrap s1 s2 $ TyCon (Var name)
    ltOf = branch "variable lifetime" do
      s1 <- getSourcePos
      C.char '\''
      name <- rawLowerText
      s2 <- getSourcePos
      space
      pure $ wrap s1 s2 $ LtOf (Var name)
    refTy = branch "reference type" do
      s1 <- getSourcePos
      refw
      t1 <- simpleTy
      t2 <- simpleTy
      pure $ wrap s1 t2 $ RefTy t1 t2
    univTy = branch "polymorphic type" do
      s1 <- getSourcePos
      forallw
      m <- mult
      space
      lts <- simpleTy
      tyVarName <- lowerText
      colonw
      k <- kindp
      dotw
      outTy <- ty
      pure $ wrap s1 outTy $ Univ m lts (TyVarBinding tyVarName) k outTy

tm :: Parser Tm
tm = label "term" fullTm
  where
    fullTm = do
      t1 <- subTm
      anno t1 <|> apps t1 <|> pure t1
    tyApps t1 = label "type applications" do
      let tyArg tys = do
            C.char '['
            space
            t <- ty
            C.char ']'
            s1 <- getSourcePos
            space
            tyArg (t:tys) <|> pure (wrap t1 s1 $ AppTy t1 $ reverse $ t:tys)
      tyArg []
    termApps t1 = try $ label "term applications" do
      args <- some subTm
      let f l r = wrap t1 r $ AppTm l r
      pure $ foldl' f t1 args
    apps t1 = do
      t2 <- tyApps t1 <|> pure t1
      termApps t2 <|> pure t2
    anno term = label "type annotation" do
      colonw
      termTy <- ty
      pure $ wrap term termTy $ Anno term termTy
    subTm = choice [tmVar, paren, caseTm, letStruct, letVar,
             tmCon, copy, refTm, drop, intLit, stringLit, funTm]
    paren = label "term parentheses" $ lexeme $ C.char '(' *> space *> tm <* C.char ')'
    intLit = label "integer literal" $ lexeme $ try do
      s1 <- getSourcePos
      isNeg <- isJust <$> optional (C.char '-')
      i <- L.decimal
      s2 <- getSourcePos
      pure $ wrap s1 s2 $ LiteralTm (IntLit (if isNeg then negate i else i))
    stringLit = label "string literal" $ lexeme do
      s1 <- getSourcePos
      C.char '"'
      str <- manyTill L.charLiteral (C.char '"')
      s2 <- getSourcePos
      pure $ wrap s1 s2 $ LiteralTm (StringLit (T.pack str))
    caseBranch = label "case branch" do
      barw
      con <- upperSVar
      vars <- many lowerSVar
      arroww
      body <- tm
      pure $ CaseBranch con vars body
    caseTm = label "case expression" do
      st <- getSourcePos
      casew
      val <- tm
      ofw
      branches <- some caseBranch
      let (CaseBranch _ _ endTm) = last branches
      pure $ wrap st endTm $ Case val branches
    letStruct = label "let struct" do
      st <- getSourcePos
      try $ letw *> lookAhead C.upperChar
      con <- upperSVar
      vars <- many lowerSVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ wrap st body $ LetStruct con vars val body
    letVar = label "let var" do
      st <- getSourcePos
      try $ letw *> lookAhead C.lowerChar
      var <- lowerSVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ wrap st body $ Let var val body
    tyBinds = many do
      keyword "["
      bind <- TyVarBinding <$> lowerText
      colonw
      k <- kindp
      keyword "]"
      pure (bind, k)
    argBareBind = (\v-> (v, Nothing)) <$> lowerSVar
    argTyBind = do
      keyword "("
      argVar <- lowerSVar
      colonw
      argTy <- ty
      keyword ")"
      pure (argVar, Just argTy)
    funTm = label "term function" do
      st <- getSourcePos
      fixFun <- optional $ recw *> lowerSVar
      funw
      polyB <- tyBinds
      argB <- some $ argTyBind <|> argBareBind
      arroww
      body <- tm
      pure $ wrap st body $ FunTm fixFun polyB argB body
    tmVar = label "term variable" $ try do
      (SVar v s) <- lowerSVar
      pure $ Tm s $ TmVar v
    copy = label "copy" $ varPredUtil copyw Copy
    refTm = label "term reference" $ varPredUtil refw RefTm
    tmCon = branch "enum constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ wrap s1 s2 $ TmCon (Var name)
    drop = label "drop" do
      s1 <- getSourcePos
      dropw
      var <- lowerSVar
      inw
      body <- tm
      pure $ wrap s1 body $ Drop var body

decl :: Parser Decl
decl = choice [funDecl, enumDecl, structDecl] where
  typeParams = label "type parameters" $ mkParens do
    name <- lowerText
    colonw
    k <- kindp
    pure $ TypeParam name k
  funDecl = label "function declaration" do
    s1 <- getSourcePos
    name <- try $ lowerText <* colonw
    funTy <- ty
    equalw
    funBody <- tm
    semicolonw
    space
    pure $ FunDecl name funTy funBody $ s1 `spanTo` funBody
  enumCon = do
    name <- upperText
    args <- many simpleTy
    pure $ EnumCon name args
  enumDecl = label "enum declaration" do
    s1 <- getSourcePos
    enumw
    name <- upperText
    tyP <- many typeParams
    equalw
    cons <- enumCon `sepBy` barw
    semicolonw
    -- TODO: switch to properly pulling the last source from the cons
    s2 <- getSourcePos
    space
    pure $ EnumDecl name tyP cons $ spanBetween s1 s2
  structDecl = label "struct declaration" do
    s1 <- getSourcePos
    structw
    name <- upperText
    tyP <- many typeParams
    keyword "{"
    members <- many simpleTy
    keyword "}"
    s2 <- getSourcePos
    space
    pure $ StructDecl name tyP members $ spanBetween s1 s2

fileDecls :: Parser [Decl]
fileDecls = space *> some decl <* eof
