{-# LANGUAGE EmptyDataDeriving, OverloadedRecordDot #-}
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

lineComment = L.skipLineComment "//"
blockComment = L.skipBlockCommentNested "/*" "*/"

space :: Parser ()
space = L.space C.space1 lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

spanBetween :: SourcePos -> SourcePos -> Span
spanBetween (SourcePos filePath sl sc) (SourcePos _ el ec) =
  Span filePath (unPos sl) (unPos sc) (unPos el) (unPos ec)

wrapSpan :: Parser (Span -> a) -> Parser a
wrapSpan m = do
  s1 <- getSourcePos
  v <- m
  s2 <- getSourcePos
  pure $ v $ spanBetween s1 s2

validateForKeywords :: Parser Text -> Parser Text
validateForKeywords m = do
  sp <- getSourcePos
  txt <- m
  if txt `elem` keywords
    then customFailure $ VarIsKeyword txt
    else pure $ txt

mkVarParser :: Parser Char -> Parser Text
mkVarParser m = validateForKeywords $ T.cons <$> m <*> takeWhileP Nothing Char.isAlphaNum
-- mkVarParser m = validateForKeywords $ fmap T.pack $ (:) <$> m <*> many C.alphaNumChar

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

varPredUtil :: Parser () -> (Var -> Span -> a) -> Parser a
varPredUtil pred f = lexeme do
  s1 <- getSourcePos
  pred
  txt <- rawLowerText
  s2 <- getSourcePos
  pure $ f (Var txt) $ spanBetween s1 s2

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
polyw = keyword "^"
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

spanTo :: Spans a => SourcePos -> a -> Span
spanTo (SourcePos _ sl sc) sp = (getSpan sp) {startLine = unPos sl, startColumn = unPos sc}

spanFrom :: Spans a => a -> SourcePos -> Span
spanFrom sp (SourcePos _ el ec) = (getSpan sp) {endLine=unPos el, endColumn = unPos ec}

spanFromTo :: (Spans a, Spans b) => a -> b -> Span
spanFromTo start end = f (getSpan start) (getSpan end) where
  f s Span{..} = s{endLine=endLine, endColumn=endColumn}

mkParens :: Parser a -> Parser a
mkParens = between (keyword "(") (keyword ")")

kindp :: Parser Kind
kindp = do
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
ty = do
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
      pure $ FunTy m t1 lts t2 $ t1 `spanFromTo` t2
    tyApp t1 = branch "type operator arguments" do
      args <- some simpleTy
      let f t1 t2 = TyApp t1 t2 $ t1 `spanFromTo` t2
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
  pure $ LtJoin ltParts $ spanBetween s1 s2

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
      pure $ TyVar (MkTyVar name 0) $ spanBetween s1 s2
    tyCon = branch "type constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ TyCon (Var name) $ spanBetween s1 s2
    ltOf = branch "variable lifetime" do
      s1 <- getSourcePos
      C.char '\''
      name <- rawLowerText
      s2 <- getSourcePos
      space
      pure $ LtOf (Var name) $ spanBetween s1 s2
    refTy = branch "reference type" do
      s1 <- getSourcePos
      refw
      t1 <- simpleTy
      t2 <- simpleTy
      pure $ RefTy t1 t2 $ s1 `spanTo` t2
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
      pure $ Univ m lts (TyVarBinding tyVarName) k outTy $ s1 `spanTo` outTy

tm :: Parser Tm
tm = fullTm
  where
    fullTm = do
      t1 <- subTm
      anno t1 <|> apps t1 <|> pure t1
    apps t1 = branch "argument applications" do
      let tyArg = do
            C.char '['
            space
            t <- ty
            C.char ']'
            s2 <- getSourcePos
            space
            pure $ Right (t, s2)
      args <- some $ tyArg <|> (Left <$> subTm)
      space
      let f l (Left r) = AppTm l r $ t1 `spanFromTo` r
          f l (Right (r, s2)) = AppTy l r $ t1 `spanFrom` s2
      pure $ foldl' f t1 args
    anno term = label "type annotation" do
      colonw
      termTy <- ty
      pure $ Anno term termTy $ term `spanFromTo` termTy
    subTm = choice [tmVar, paren, caseTm, letStruct, letVar,
             tmCon, copy, refTm, drop, intLit, stringLit,
             fixTm, funTm, poly]
    paren = label "term parentheses" $ lexeme $ C.char '(' *> space *> tm <* C.char ')'
    intLit = label "integer literal" $ lexeme $ try do
      s1 <- getSourcePos
      isNeg <- isJust <$> optional (C.char '-')
      i <- L.decimal
      s2 <- getSourcePos
      pure $ LiteralTm (IntLit (if isNeg then negate i else i)) $ spanBetween s1 s2
    stringLit = label "string literal" $ lexeme do
      s1 <- getSourcePos
      C.char '"'
      str <- manyTill L.charLiteral (C.char '"')
      s2 <- getSourcePos
      pure $ LiteralTm (StringLit (T.pack str)) $ spanBetween s1 s2
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
      pure $ Case val branches $ st `spanTo` endTm
    letStruct = label "let struct" do
      st <- getSourcePos
      try $ letw *> lookAhead C.upperChar
      con <- upperSVar
      vars <- many lowerSVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ LetStruct con vars val body $ st `spanTo` body
    letVar = label "let var" do
      st <- getSourcePos
      try $ letw *> lookAhead C.lowerChar
      var <- lowerSVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ Let var val body $ st `spanTo` body
    funAnno = (Just <$> (colonw *> ty)) <|> pure Nothing
    funTm = label "term function" do
      st <- getSourcePos
      funw
      arg <- lowerSVar
      anno <- funAnno
      arroww
      body <- tm
      pure $ FunTm arg anno body $ st `spanTo` body
    poly = label "polymorphism term" do
      st <- getSourcePos
      polyw
      let pbind = try do
            bind <- TyVarBinding <$> lowerText
            colonw
            k <- kindp
            dotw
            pure $ Just (bind, k)
      mbBind <- pbind <|> pure Nothing
      body <- tm
      pure $ Poly mbBind body $ st `spanTo` body
    tmVar = label "term variable" $ try do
      (SVar v s) <- lowerSVar
      pure $ TmVar v s
    copy = label "copy" $ varPredUtil copyw Copy
    refTm = label "term reference" $ varPredUtil refw RefTm
    tmCon = branch "enum constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ TmCon (Var name) $ spanBetween s1 s2
    drop = label "drop" do
      s1 <- getSourcePos
      dropw
      var <- lowerSVar
      inw
      body <- tm
      pure $ Drop var body $ s1 `spanTo` body
    fixTm = label "recursive function" do
      s1 <- getSourcePos
      recw
      funVar <- lowerSVar
      arroww
      body <- tm
      pure $ FixTm funVar body $ s1 `spanTo` body

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
