{-# LANGUAGE QuasiQuotes #-}
module Rll.GenSpec where

import QuoteTxt
import Rll.ScSpecUtil (parseFile')
import Rll.GenLLVM

import LLVM.Context qualified as L
import LLVM.Module qualified as L
import LLVM.AST qualified as A
import LLVM.AST.DataLayout qualified as A

import Data.Text (Text)
import Data.ByteString.Char8 qualified as BS
import Test.Hspec

willGen :: Text -> Expectation
willGen txt = do
  mbSpecDecls <- parseFile' txt
  case mbSpecDecls of
    Nothing -> pure ()
    Just (order, specDecls) -> L.withContext \ctx -> do
      let layout = A.defaultDataLayout A.LittleEndian
      result <- runGen specDecls order ctx layout
      case result of
        Left err -> expectationFailure $ "Gen error: " <> show err
        Right defs -> do
          let mod = A.Module "test" "test.rll" (Just layout) Nothing defs
          -- print $ "defs: " <> show defs
          llvm <- L.withModuleFromAST ctx mod L.moduleLLVMAssembly
          BS.putStrLn llvm

spec :: Spec
spec = do
  describe "generate llvm" do
    it "can run" do
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }

        extractRight : forall M [] l:Lifetime. forall M [] a:Type. forall M [] b:Type.
          &l (a -M[]> Unit) -M[]> ((Tuple a b) -S[l]> b)
        = \destroyLeft tup ->
        let Tuple left right = tup in
        let Unit = destroyLeft left in
        right;

        enum Two = Left L | Right R;

        main : Two
        = let tup = Tuple [L] [R] L (R Unit Unit) in
        let destroyL = \(l:L) -> let L = l in Unit in
        let v = Right (extractRight ['destroyL] [L] [R] &destroyL tup) in
        drop destroyL in v;
        |]
