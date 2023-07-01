{-# LANGUAGE QuasiQuotes #-}
module Rll.GenSpec where

import QuoteTxt
import Rll.ScSpecUtil (parseFile)
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
  mbSpecDecls <- parseFile txt
  case mbSpecDecls of
    Nothing -> pure ()
    Just specDecls -> L.withContext \ctx -> do
      let layout = A.defaultDataLayout A.LittleEndian
      result <- runGen specDecls ctx layout
      case result of
        Left err -> expectationFailure $ show err
        Right defs -> do
          let mod = A.Module "test" "test.rll" (Just layout) Nothing defs
          print $ "defs: " <> show defs
          llvm <- L.withModuleFromAST ctx mod L.moduleLLVMAssembly
          BS.putStrLn llvm

spec :: Spec
spec = do
  describe "generate llvm" do
    it "can run" do
      willGen [txt|
        struct L { String }

        struct R { I64 }

        enum Two = Left L | Right R;

        main : Two = Left (L "test");
        |]
