{-# LANGUAGE QuasiQuotes #-}
module Rll.ParserSpec where

import Test.Hspec
import qualified Data.Text as T
import Data.Text (Text)
import qualified Text.Megaparsec as M
import Data.Either (isLeft)
import System.Timeout (timeout)
import Control.Monad (unless)

import QuoteTxt
import Rll.AstUtil

import Rll.Parser
import Rll.Ast

mkParserChecker :: (HasCallStack, Show a, Eq a) => Parser a -> a -> T.Text -> Expectation
mkParserChecker p v text = case M.parse (p <* M.eof) "test.rll" text of
  Right v' -> v' `shouldBe` v
  Left err -> expectationFailure $ M.errorBundlePretty err

tmFrom :: (HasCallStack) => Tm -> T.Text -> Expectation
tmFrom = mkParserChecker tm

tyFrom :: (HasCallStack) => Ty -> T.Text -> Expectation
tyFrom = mkParserChecker ty

declFrom :: (HasCallStack) => Decl -> T.Text -> Expectation
declFrom = mkParserChecker decl

parseShouldError :: (Show a, Eq a) => Parser a -> T.Text -> Expectation
parseShouldError p t = do
  let result = M.parse (p <* M.eof) "test.rll" t
  unless (isLeft result) $ expectationFailure "should have parse error"

-- | Just checks to make sure that there are no errors parsing the file.
canParse :: Text -> Expectation
canParse text = do
  result <- timeout delay attempt
  case result of
    Nothing -> expectationFailure "Timed out"
    Just _ -> pure ()
  where
    delay = 10^6 -- one minute
    attempt = case M.parse fileDecls "test.rll" text of
      Left err -> expectationFailure $ M.errorBundlePretty err
      Right _ -> pure ()

spec :: Spec
spec = parallel do
  describe "tm" do
    it "parses terms in parentheses" do
      tmCon "Unit" `tmFrom` "(   (Unit   ))"
    it "parses case expressions" do
      let t = tmCase (tmVar "x") [br ["True"] $ tmVar "y", br ["False"] $ tmVar "z"]
      t `tmFrom` "case x of | True -> y | False -> z"
      -- TODO: I need to make a list of excluded keywords for the variable parsers.
    it "parses let struct" do
      let t = letStruct ["Pair", "x", "y"] (tmVar "pairVar") body
          body = appTm (tmVar "x") (tmVar "y")
      t `tmFrom` "let Pair x y = pairVar in x y"
    it "parses let var" do
      let t = tmLet "x" (tmVar "y") (tmVar "x")
      t `tmFrom` "let x = y in x"
    it "parses term function" do
      let t1 = funTm [] [argT "x" $ tyCon "Unit"] $ tmVar "x"
          t2 = funTm [] [argI "x"] $ tmVar "x"
      t1 `tmFrom` "\\(x : Unit) -> x"
      t2 `tmFrom` "\\x -> x"
    it "parses a polymorphic function" do
      let t1 = funTm [argK "l" LtKind] [argI "x"] $ tmVar "y"
          t2 = funTm [argK "t" TyKind] [argT "x" $ tyVar0 "t"] $ tmVar "x"
      t1 `tmFrom` "\\ [l:Lifetime] x -> y"
      t2 `tmFrom` "\\ [t:Type] (x:t) -> x"
    it "parses term variable" do
      tmVar "x" `tmFrom` "x"
    it "parses copy" do
      copy "x" `tmFrom` "copy x"
    it "parses a reference" do
      ref "x" `tmFrom` "&x"
    it "parses term constructors" do
      tmCon "Unit" `tmFrom` "Unit"
      appTm (appTm (tmCon "Pair") (tmCon "Int")) (tmCon "Str") `tmFrom` "Pair Int Str"
    it "parses type application" do
      let t1 = appTy (tmVar "x") [tyCon "Bool"]
          t2 = appTy (tmVar "x") [tyCon "Bool", tyCon "Int"]
      t1 `tmFrom` "x [Bool]"
      t2 `tmFrom` "x [Bool] [Int]"
    it "parses drop" do
      dropv "x" (tmVar "y") `tmFrom` "drop x in y"
    it "parses function application" do
      appTm (tmVar "x") (tmVar "y") `tmFrom` "x y"
    it "parses recursive functions" do
      let t1 = fixFunTm "f" [] [argI "x"] $ tmVar "x"
          t2 = fixFunTm "f" [argK "l" LtKind] [argI "x"] $ tmVar "x"
      t1 `tmFrom` "rec f \\ x -> x"
      t2 `tmFrom` "rec f \\ [l:Lifetime] x -> x"
    it "parses type application" do
      anno (tmVar "x") (tyCon "Bool") `tmFrom` "x : Bool"
    it "parses an integer literal" do
      intL 51 `tmFrom` "51"
      intL (-47) `tmFrom` "-47"
      parseShouldError tm "- 13"
    it "parses a string literal" do
      let t = strL "hello darkness my old friend"
      t `tmFrom` [txt|"hello darkness my old friend"|]
    it "throws an error for nonsense" do
      -- TODO: seems to badly infinite loop and grow and run everything out of resources?
      parseShouldError tm "!@#@! "

  describe "ty" do
    let ltJoinXY = ltJoin [ltOf "x", ltOf "y"]
        unitTy = tyCon "Unit"
    it "parses the unit type" do
      unitTy `tyFrom` "Unit "
      unitTy `tyFrom` "Unit"
    it "parses a type variable" do
      tyVar0 "x" `tyFrom` "x "
    it "can parse a type constructor" do
      tyCon "Bool" `tyFrom` "Bool"
    it "parses in parentheses" do
      unitTy `tyFrom` "((Unit))"
      ltOf "y" `tyFrom` "( ( 'y) )"
    it "parses a lifetime" do
      ltOf "x" `tyFrom` "'x "
    it "parses a lifetime join" do
      ltJoinXY `tyFrom` "[ 'x , 'y ] "
      ltJoinXY `tyFrom` "['x , 'y] "
      ltJoinXY `tyFrom` "['x,'y]"
    it "parses a function lifetime" do
      let t = funTy Single unitTy ltJoinXY unitTy
      t `tyFrom` "Unit-S['x,'y]>Unit"
      t `tyFrom` "Unit -S[ 'x, 'y ]> Unit"
      t `tyFrom` "Unit -S [ 'x, 'y ] > Unit"
    it "parses a reference type" do
      refVar "x" unitTy `tyFrom` "&'x Unit"
    it "parses a polymorphic type" do
      let t = univ Single ltJoinXY "a" TyKind unitTy
      t `tyFrom` "forall S ['x,'y] a : Type. Unit"
    it "ignores block comments" do
      let t = univ Single ltJoinXY "a" TyKind unitTy
      t `tyFrom` "forall S ['x,'y] /*THIS IS A COMMENT*/ a : Type. Unit"
    it "ignores line comments" do
      let t = univ Single ltJoinXY "a" TyKind unitTy
      t `tyFrom` "forall S ['x,'y]a : Type. Unit // COMMENT"
    it "throws an error for nonsense" do
      parseShouldError ty "!@#@! "

  describe "decl" do
    let tyKind v = TypeParam v TyKind
    it "parses function declarations" do
      let t = FunDecl "test" (tyCon "Bool") (tmVar "b") es
      t `declFrom` "test : Bool = b;"
    it "parses enum declarations" do
      let t1 = EnumDecl "Either" [tyKind "a", tyKind "b"] [l, r] es
          l = EnumCon "Left" [tyVar0 "a"]
          r = EnumCon "Right" [tyVar0 "b", tyVar0 "c"]
          t2 = EnumDecl "Bool" [] [EnumCon "False" [], EnumCon "True" []] es
      t1 `declFrom` "enum Either (a:Type) (b:Type) = Left a | Right b c;"
      t2 `declFrom` "enum Bool = False | True;"
    it "parses struct declarations" do
      let t1 = StructDecl "Pair" [tyKind "a", tyKind "b"] [tyVar0 "a", tyVar0 "b"] es
          t2 = StructDecl "IS" [] [tyCon "Int", tyCon "Str"] es
      t1 `declFrom` "struct Pair (a:Type) (b:Type) { a b }"
      t2 `declFrom` "struct IS { Int Str }"
    it "throws an error for nonsense" do
      parseShouldError decl "!@#@! "

  describe "file" do
    it "should parse functions quickly" do
      canParse [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let u3 = Unit in
        let u4 = Unit in
        let u5 = Unit in
        let u6 = Unit in
        let s1 = Str in
        let s2 = Str in
        let i1 = Int in
        let s3 = Str in
        let Unit = u1 in
        let Unit = u5 in
        let Unit = u6 in
        let Str = s3 in
        let Str = s2 in
        let Unit = u2 in
        let Unit = u3 in
        let Unit = u4 in
        let Int = i1 in
        let Str = s1 in
        Unit;
        |]


