{-# LANGUAGE QuasiQuotes #-}
module Rll.ParserSpec where

import Test.Hspec
import qualified Data.Text as T
import Data.Text (Text)
import qualified Text.Megaparsec as M
import Data.Either (isLeft)

import QuoteTxt
import Rll.Parser
import Rll.Ast

mkParserChecker :: (Show a, Eq a) => Parser a -> a -> T.Text -> Expectation
mkParserChecker p v text = case M.parse (p <* M.eof) "test.rll" text of
  Right v' -> v' `shouldBe` v
  Left err -> expectationFailure $ M.errorBundlePretty err

es :: Span
es = Span "test.rll" M.pos1 M.pos1 M.pos1 M.pos1

tmFrom = mkParserChecker tm
tyFrom = mkParserChecker ty
declFrom = mkParserChecker decl

parseShouldError :: (Show a, Eq a) => Parser a -> T.Text -> Expectation
parseShouldError p t = do
  let result = M.parse (p <* M.eof) "test.rll" t
  result `shouldSatisfy` isLeft

spec :: Spec
spec = do
  describe "tm" do
    let tmVar n = TmVar (Var n) es
    it "parses terms in parentheses" do
      TmCon (Var "Unit") es `tmFrom` "(   (Unit   ))"
    it "parses case expressions" do
      let t = Case (tmVar "x") [b1, b2] es
          b1 = CaseBranch (Var "True") [] (tmVar "y")
          b2 = CaseBranch (Var "False") [] (tmVar "z")
      t `tmFrom` "case x of | True -> y | False -> z"
      -- TODO: I need to make a list of excluded keywords for the variable parsers.
    it "parses let struct" do
      let t = LetStruct (Var "Pair") [Var "x", Var "y"] (TmVar (Var "pairVar") es) body es
          body = AppTm (TmVar (Var "x") es) (TmVar (Var "y") es) es
      t `tmFrom` "let Pair x y = pairVar in x y"
    it "parses let var" do
      let t = Let (Var "x") (TmVar (Var "y") es) (TmVar (Var "x") es) es
      t `tmFrom` "let x = y in x"
    it "parses term function" do
      let t a = FunTm (Var "x") a (TmVar (Var "x") es) es
          t1 = t $ Just $ TyCon (Var "Unit") es
          t2 = t Nothing
      t1 `tmFrom` "\\x : Unit -> x"
      t2 `tmFrom` "\\x -> x"
    it "parses a polymorphic abstraction" do
      let t = Poly (TyVarBinding "x") LtKind (TmVar (Var "y") es) es
      t `tmFrom` "^x:Lifetime -> y"
    it "parses term variable" do
      tmVar "x" `tmFrom` "x"
    it "parses copy" do
      Copy (Var "x") es `tmFrom` "copy x"
    it "parses a reference" do
      RefTm (Var "x") es `tmFrom` "&x"
    it "parses term constructors" do
      TmCon (Var "Unit") es `tmFrom` "Unit"
    it "parses type application" do
      let t = AppTy (tmVar "x") (TyCon (Var "Bool") es) es
      t `tmFrom` "x [Bool]"
    it "parses drop" do
      Drop (Var "x") (tmVar "y") es `tmFrom` "drop x in y"
    it "parses function application" do
      AppTm (tmVar "x") (tmVar "y") es `tmFrom` "x y"
    it "parses recursive functions" do
      let t = RecFun (Var "f") (Var "l") (Var "x") (tmVar "x") es
      t `tmFrom` "fun x (l;f) x"
    it "parses type application" do
      Anno (tmVar "x") (TyCon (Var "Bool") es) es `tmFrom` "x : Bool"
    it "throws an error for nonsense" do
      -- TODO: seems to badly infinite loop and grow and run everything out of resources?
      parseShouldError tm "!@#@! "
  describe "ty" do
    let ltJoinXY = LtJoin [LtOf (Var "x") es, LtOf (Var "y") es] es
        unitTy = TyCon (Var "Unit") es
    it "parses the unit type" do
      unitTy `tyFrom` "Unit "
      unitTy `tyFrom` "Unit"
    it "parses a type variable" do
      TyVar (MkTyVar "x" 0) es `tyFrom` "x "
    it "can parse a type constructor" do
      TyCon (Var "Bool") es `tyFrom` "Bool"
    it "parses in parentheses" do
      unitTy `tyFrom` "((Unit))"
      LtOf (Var "y") es `tyFrom` "( ( 'y) )"
    it "parses a lifetime" do
      LtOf (Var "x") es `tyFrom` "'x "
    it "parses a lifetime join" do
      ltJoinXY `tyFrom` "[ 'x , 'y ] "
      ltJoinXY `tyFrom` "['x , 'y] "
      ltJoinXY `tyFrom` "['x,'y]"
    it "parses a function lifetime" do
      let t = FunTy Single unitTy ltJoinXY unitTy es
      t `tyFrom` "Unit-S['x,'y]>Unit"
      t `tyFrom` "Unit -S[ 'x, 'y ]> Unit"
      parseShouldError ty "Unit -S [ 'x, 'y ] > Unit"
    it "parses a reference type" do
      RefTy (LtOf (Var "x") es) unitTy es `tyFrom` "&'x Unit"
    it "parses a polymorphic type" do
      let t = Univ Single ltJoinXY (TyVarBinding "a") TyKind unitTy es
      t `tyFrom` "forall S ['x,'y] a : Type. Unit"
    it "throws an error for nonsense" do
      parseShouldError ty "!@#@! "
  describe "decl" do
    let tyCon t = TyCon (Var t) es
        tyVar n = TyVar (MkTyVar n 0) es
        tmVar n = TmVar (Var n) es
    it "parses function declarations" do
      let t = FunDecl "test" (tyCon "Bool") (tmVar "b") es
      t `declFrom` "test : Bool = b"
    it "parses enum declarations" do
      let t1 = EnumDecl "Either" [l, r] es
          l = EnumCon "Left" [tyVar "a"]
          r = EnumCon "Right" [tyVar "b", tyVar "c"]
          t2 = EnumDecl "Bool" [EnumCon "False" [], EnumCon "True" []] es
      t1 `declFrom` "enum Either = Left a | Right b c"
      t2 `declFrom` "enum Bool = False | True"
    it "parses struct declarations" do
      let t = StructDecl "Pair" [tyVar "a", tyVar "b"] es
      t `declFrom` "struct Pair { a b }"
    it "throws an error for nonsense" do
      parseShouldError decl "!@#@! "


