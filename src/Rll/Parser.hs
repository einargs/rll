{-# LANGUAGE EmptyDataDeriving #-}
module Rll.Parser (
  Parser, decl, fileDecls, tm, ty, RllParseError(..),
) where

import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Functor (($>))
import Control.Monad (void)
import Text.Megaparsec.Debug

import Rll.Ast

data RllParseError
  = VarIsKeyword Text
  deriving (Show, Eq, Ord)

instance ShowErrorComponent RllParseError where
  showErrorComponent (VarIsKeyword txt) = T.unpack txt <> " cannot be a keyword."

type Parser = Parsec RllParseError Text

lineComment = L.skipLineComment "//"
blockComment = L.skipBlockCommentNested "/*" "*/"

space :: Parser ()
space = L.space C.space1 lineComment blockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

spanBetween :: SourcePos -> SourcePos -> Span
spanBetween (SourcePos filePath sl sc) (SourcePos _ el ec) = Span filePath sl sc el ec

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

rawUpperText :: Parser Text
rawUpperText = validateForKeywords $ fmap T.pack $ (:) <$> C.upperChar <*> many C.alphaNumChar

upperText :: Parser Text
upperText = lexeme rawUpperText

rawLowerText :: Parser Text
rawLowerText = validateForKeywords $ fmap T.pack $ (:) <$> C.lowerChar <*> many C.alphaNumChar

lowerText :: Parser Text
lowerText = lexeme $ rawLowerText

upperVar = Var <$> upperText
lowerVar = Var <$> lowerText

varPredUtil :: Parser () -> (Var -> Span -> a) -> Parser a
varPredUtil pred f = do
  s1 <- getSourcePos
  pred
  txt <- rawLowerText
  s2 <- getSourcePos
  space
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
recfunw = keyword "fun"
commaw = keyword ","
enumw = keyword "enum"
structw = keyword "struct"
forallw = keyword "forall"
dotw = keyword "."

keywords :: [Text]
keywords = ["let", "in", "case", "copy", "drop", "fun", "enum", "forall", "struct", "of"]

spanTo :: Spans a => SourcePos -> a -> Span
spanTo (SourcePos _ sl sc) sp = (getSpan sp) {startLine = sl, startColumn = sc}

kind :: Parser Kind
kind = keyword "Type" $> TyKind <|> keyword "Lifetime" $> LtKind

mult :: Parser Mult
mult = C.char 'S' $> Single <|> C.char 'M' $> Many

branch :: Show a => String -> Parser a -> Parser a
branch name = try . label name

ty :: Parser Ty
ty = funTy <|> subTy
  where
    subTy = choice [univTy, tyVar, tyCon, ltOf, ltJoin, refTy, parenTy]
    parenTy = branch "type level parentheses" $ lexeme $ C.char '(' *> space *> ty <* C.char ')'
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
    ltJoin = rawLtJoin <* space
    rawLtJoin = branch "lifetime join" do
      s1 <- getSourcePos
      C.char '['
      space
      ltParts <- ty `sepBy` commaw
      C.char ']'
      s2 <- getSourcePos
      pure $ LtJoin ltParts $ spanBetween s1 s2
    funTy = branch "function type" do
      s1 <- getSourcePos
      t1 <- subTy
      C.char '-'
      m <- mult
      space
      lts <- rawLtJoin
      C.char '>'
      space
      t2 <- ty
      pure $ FunTy m t1 lts t2 $ s1 `spanTo` t2
    refTy = label "reference type" do
      s1 <- getSourcePos
      refw
      t1 <- ty
      t2 <- ty
      pure $ RefTy t1 t2 $ s1 `spanTo` t2
    univTy = label "polymorphic type" do
      s1 <- getSourcePos
      forallw
      m <- mult
      space
      lts <- ty
      tyVarName <- lowerText
      colonw
      k <- kind
      dotw
      outTy <- ty
      pure $ Univ m lts (TyVarBinding tyVarName) k outTy $ s1 `spanTo` outTy
      -- TODO finish ty, then test.

tm :: Parser Tm
tm = choice [appTy, appTm, anno, subTm]
  where
    subTm = choice [paren, caseTm, letStruct,
             tmVar, tmCon, copy, refTm, drop,
             recFun, letVar, funTm, poly]
    paren = branch "term parentheses" $ lexeme $ C.char '(' *> space *> tm <* C.char ')'
    caseBranch = label "case branch" do
      barw
      con <- upperVar
      vars <- many lowerVar
      arroww
      body <- tm
      pure $ CaseBranch con vars body
    caseTm = label "case expression" do
      st <- getSourcePos
      casew
      val <- tm
      ofw
      branches <- some caseBranch
      let (CaseBranch _ _ endTm) = head branches
      pure $ Case val branches $ st `spanTo` endTm
    letStruct = branch "let struct" do
      st <- getSourcePos
      letw
      con <- upperVar
      vars <- many lowerVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ LetStruct con vars val body $ st `spanTo` body
    letVar = branch "let var" do
      st <- getSourcePos
      letw
      var <- lowerVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ Let var val body $ st `spanTo` body
    funAnno = (Just <$> (colonw *> ty)) <|> pure Nothing
    funTm = branch "term function" do
      st <- getSourcePos
      funw
      arg <- lowerVar
      anno <- funAnno
      arroww
      body <- tm
      pure $ FunTm arg anno body $ st `spanTo` body
    poly = branch "polymorphism term" do
      st <- getSourcePos
      polyw
      bind <- TyVarBinding <$> lowerText
      colonw
      k <- kind
      arroww
      body <- tm
      pure $ Poly bind k body $ st `spanTo` body
    tmVar = branch "term variable" $ varPredUtil (pure ()) TmVar
    copy = label "copy" $ varPredUtil copyw Copy
    refTm = label "term reference" $ varPredUtil refw RefTm
    tmCon = branch "enum constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ TmCon (Var name) $ spanBetween s1 s2
    appTy = branch "apply type" do
      s1 <- getSourcePos
      f <- subTm
      C.char '['
      space
      t <- ty
      C.char ']'
      space
      pure $ AppTy f t $ s1 `spanTo` t
    drop = label "drop" do
      s1 <- getSourcePos
      dropw
      var <- lowerVar
      inw
      body <- tm
      pure $ Drop var body $ s1 `spanTo` body
    appTm = branch "function application" do
      s1 <- getSourcePos
      t1 <- subTm
      t2 <- tm
      pure $ AppTm t1 t2 $ s1 `spanTo` t2
    recFun = label "recursive function" do
      s1 <- getSourcePos
      recfunw
      funVar <- lowerVar
      keyword "("
      funLtVar <- lowerVar
      keyword ";"
      arg <- lowerVar
      keyword ")"
      body <- tm
      pure $ RecFun arg funLtVar funVar body $ s1 `spanTo` body
    anno = branch "type annotation" do
      s1 <- getSourcePos
      term <- subTm
      colonw
      termTy <- ty
      pure $ Anno term termTy $ s1 `spanTo` termTy

decl :: Parser Decl
decl = choice [funDecl, enumDecl, structDecl] where
  funDecl = branch "function declaration" do
    s1 <- getSourcePos
    name <- lowerText
    colonw
    funTy <- ty
    equalw
    funBody <- tm
    pure $ FunDecl name funTy funBody $ s1 `spanTo` funBody
  enumCon = do
    name <- upperText
    args <- many ty
    pure $ EnumCon name args
  enumDecl = label "enum declaration" do
    s1 <- getSourcePos
    enumw
    name <- upperText
    equalw
    cons <- enumCon `sepBy` barw
    -- TODO: switch to properly pulling the last source from the cons
    s2 <- getSourcePos
    pure $ EnumDecl name cons $ spanBetween s1 s2
  structDecl = label "struct declaration" do
    s1 <- getSourcePos
    structw
    name <- upperText
    keyword "{"
    members <- many ty
    keyword "}"
    s2 <- getSourcePos
    space
    pure $ StructDecl name members $ spanBetween s1 s2

fileDecls :: Parser [Decl]
fileDecls = space *> some decl
