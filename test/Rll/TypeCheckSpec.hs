{-# LANGUAGE BlockArguments, OverloadedStrings #-}
module Rll.TypeCheckSpec where

import Test.Hspec
import qualified Data.Text as T

import Rll.TypeCheck
import Rll.Ast

mkVars :: T.Text -> [Var]
mkVars ts = uncurry Var <$> zip (T.splitOn " " ts) [0..]

synthTo :: Tm -> Ty -> Expectation
synthTo tm ty = runTc emptyCtx (synth tm) `shouldBe` Right ty

checkTo :: Tm -> Ty -> Expectation
checkTo tm ty = runTc emptyCtx (check ty tm) `shouldBe` Right ()

spec :: Spec
spec = do
  let [a,b,c,d,e,f,g] = mkVars "a b c d e f g"
      sumVal = Anno (InL Unit) (SumTy UnitTy UnitTy)
      destroySum expr = Case Single expr f (TmVar f) g (TmVar g)
  describe "typechecking" do
    -- TODO tests that check what fails on synth but works with check
    it "can type check a nested product" do
      ProdTm (ProdTm Unit Unit) Unit `synthTo` ProdTy (ProdTy UnitTy UnitTy) UnitTy
    it "can check a case of" do
      let caseArm v = LetUnit (TmVar v) (ProdTm Unit Unit)
      Case Single (Anno (InL Unit) (SumTy UnitTy UnitTy)) a (caseArm a) b (caseArm b) `synthTo` ProdTy UnitTy UnitTy

    it "can borrow and drop" do
      let letExp = Let a Unit $ Let b (RefTm a) $ Drop b $ TmVar a
      letExp `synthTo` UnitTy

    it "checks that using a reference variable consumes it" do
      let arm v = Drop v Unit
          finalArm v = LetUnit (TmVar v) Unit
          letExp = Let a (Anno (InL Unit) (SumTy UnitTy UnitTy)) letBody
          caseBody = Let d (RefTm a) $ Case Many (TmVar d) b (arm b) c (arm c)
          letBody = LetUnit caseBody $ Case Single (TmVar a) d (finalArm d) e (finalArm e)

          top = Let a (ProdTm Unit Unit) $ Let d (RefTm a) $ LetProd Many b c (TmVar d) use
          use = Drop b $ Drop c $ LetProd Single b c (TmVar a) $ LetUnit (TmVar b) $ TmVar c
      letExp `synthTo` UnitTy
      top `synthTo` UnitTy

    it "can decompose a reference product" do
      let top = Let a (ProdTm Unit Unit) $ LetProd Many b c (RefTm a) $ Drop b $ Drop c use
          use = LetProd Single b c (TmVar a) $ LetUnit (TmVar b) $ TmVar c
      top `synthTo` UnitTy

    it "can check a case inside a let" do
      let arm v = Drop v Unit
          letExp = Let a (Anno (InL Unit) (SumTy UnitTy UnitTy)) letBody
          caseBody = Case Many (RefTm a) b (arm b) c (arm c)
          letBody = LetUnit caseBody $ Case Single (TmVar a) d (TmVar d) e (LetUnit (TmVar e) Unit)
      letExp `synthTo` UnitTy

    -- TODO: write check versions for these once check is implemented, since that's different.
    it "can synthesize a multiple use function type" do
      let f = FunTm a (Just UnitTy) $ TmVar a
      f `synthTo` FunTy Many UnitTy (LtJoin []) UnitTy

    it "can synth a single use function type" do
      let f = Let a Unit $ FunTm b (Just UnitTy) $ LetUnit (TmVar a) $ TmVar b
      f `synthTo` FunTy Single UnitTy (LtJoin []) UnitTy

    it "can synth a list of borrowed variables" do
      let expr = Let a sumVal $ LetUnit (AppTm f Unit) $ destroySum (TmVar a)
          arm v = Drop v $ TmVar b
          f = FunTm b (Just UnitTy) $ Case Many (RefTm a) c (arm c) d (arm d)
      expr `synthTo` UnitTy
