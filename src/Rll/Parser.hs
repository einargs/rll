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
import qualified Data.Map as M
import Data.List (foldl')

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
mkVarParser m = validateForKeywords $ fmap T.pack $ (:) <$> m <*> many C.alphaNumChar

rawUpperText :: Parser Text
rawUpperText = mkVarParser C.upperChar

rawLowerText :: Parser Text
rawLowerText = mkVarParser C.lowerChar

upperText :: Parser Text
upperText = lexeme rawUpperText

lowerText :: Parser Text
lowerText = lexeme rawLowerText

upperVar = Var <$> upperText
lowerVar = Var <$> lowerText

mkSVarParser :: Parser Text -> Parser SVar
mkSVarParser m = lexeme do
  s1 <- getSourcePos
  t <- m
  s2 <- getSourcePos
  pure $ SVar (Var t) $ spanBetween s1 s2

upperSVar = mkSVarParser rawUpperText
lowerSVar = mkSVarParser rawLowerText

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
      t1 <- subTy
      t2 <- subTy
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
tm = choice [apps, anno, subTm]
  where
    subTm = choice [paren, caseTm, letStruct,
             tmVar, tmCon, copy, refTm, drop,
             fixTm, letVar, funTm, poly]
    paren = branch "term parentheses" $ lexeme $ C.char '(' *> space *> tm <* C.char ')'
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
    letStruct = branch "let struct" do
      st <- getSourcePos
      letw
      con <- upperSVar
      vars <- many lowerSVar
      equalw
      val <- tm
      inw
      body <- tm
      pure $ LetStruct con vars val body $ st `spanTo` body
    letVar = branch "let var" do
      st <- getSourcePos
      letw
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
            k <- kind
            arroww
            pure $ Just (bind, k)
      mbBind <- pbind <|> pure Nothing
      body <- tm
      pure $ Poly mbBind body $ st `spanTo` body
    tmVar = branch "term variable" $ varPredUtil (pure ()) TmVar
    copy = label "copy" $ varPredUtil copyw Copy
    refTm = label "term reference" $ varPredUtil refw RefTm
    tmCon = branch "enum constructor" do
      s1 <- getSourcePos
      name <- rawUpperText
      s2 <- getSourcePos
      space
      pure $ TmCon (Var name) $ spanBetween s1 s2
    apps = branch "argument applications" do
      s1 <- getSourcePos
      t1 <- subTm
      let tyArg = do
            C.char '['
            space
            t <- ty
            C.char ']'
            s2 <- getSourcePos
            space
            pure $ Right (t, s2)
      args <- some $ (Left <$> subTm) <|> tyArg
      space
      let f l (Left r) = AppTm l r $ s1 `spanTo` r
          f l (Right (r, s2)) = AppTy l r $ spanBetween s1 s2
      pure $ foldl' f t1 args
      where
    appTy = branch "apply type" do
      s1 <- getSourcePos
      t1 <- subTm
      tyArgs <- some do
        C.char '['
        space
        t <- ty
        C.char ']'
        s2 <- getSourcePos
        space
        pure (t, s2)
      let f l (r, s2) = AppTy l r $ spanBetween s1 s2
      pure $ foldl' f t1 tyArgs
    drop = label "drop" do
      s1 <- getSourcePos
      dropw
      var <- lowerSVar
      inw
      body <- tm
      pure $ Drop var body $ s1 `spanTo` body
    appTm = branch "function application" do
      s1 <- getSourcePos
      t1 <- subTm
      args <- some subTm
      let f l r = AppTm l r $ s1 `spanTo` r
      pure $ foldl' f t1 args
    fixTm = label "recursive function" do
      s1 <- getSourcePos
      recw
      funVar <- lowerSVar
      arroww
      body <- tm
      pure $ FixTm funVar body $ s1 `spanTo` body
    anno = branch "type annotation" do
      s1 <- getSourcePos
      term <- subTm
      colonw
      termTy <- ty
      pure $ Anno term termTy $ s1 `spanTo` termTy

decl :: Parser Decl
decl = choice [funDecl, enumDecl, structDecl] where
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
    args <- many ty
    pure $ EnumCon name args
  enumDecl = label "enum declaration" do
    s1 <- getSourcePos
    enumw
    name <- upperText
    equalw
    cons <- enumCon `sepBy` barw
    semicolonw
    -- TODO: switch to properly pulling the last source from the cons
    s2 <- getSourcePos
    space
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
fileDecls = space *> some decl <* eof
