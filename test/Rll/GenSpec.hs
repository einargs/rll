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
    it "generates an id function" do
      willGen [txt|
        struct U2 {}
        struct Unit {}

        thing : U2 -M[]> U2
        = \ u -> u;

        main : Unit -M[]> Unit
        = \u -> u;
        |]
    it "simple bool" do
      willGen [txt|
        enum Bool = True | False;

        main : Bool -M[]> Bool
        = \b -> case b of
        | True -> False
        | False -> True;
        |]
    it "uses a polymorphic type as an argument to a polymorphic function" do
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        main : Two -M[]> L
        = \t ->
        case t of
        | Left l -> l
        | Right r ->
        let R u1 u2 = r in
        let tup = Tuple [Unit] [Unit] u1 u2 in
        let Tuple u3 u4 = id [Tuple Unit Unit] tup in
        let Unit = id [Unit] u3 in
        let Unit = u4 in
        L;
        |]
    it "uses a multi argument function" do
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : Unit -M[]> Unit -S[]> Tuple Unit Unit
        = \u1 u2 -> Tuple [Unit] [Unit] u1 u2;

        main : Two -M[]> L
        = \t ->
        case t of
        | Left l -> l
        | Right r ->
        let R u1 u2 = r in
        let tup = buildUTup u1 u2 in
        let Tuple u3 u4 = id [Tuple Unit Unit] tup in
        let Unit = id [Unit] u3 in
        let Unit = u4 in
        L;
        |]
    it "takes a function as an argument" do
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : (Unit -M[]> Unit) -M[]> Unit -S[]> Tuple Unit Unit
        = \uId u2 -> Tuple [Unit] [Unit] (uId Unit) u2;

        main : Two -M[]> L
        = \t ->
        case t of
        | Left l -> l
        | Right r ->
        let R u1 u2 = r in
        let Unit = u1 in
        let uId = id [Unit] in
        let tup = buildUTup uId u2 in
        let Tuple u3 u4 = tup in
        let Unit = u3 in
        let Unit = u4 in
        L;
        |]
    it "takes a reference to a function as an argument" do
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : forall M [] l:Lifetime. &l (Unit -M[]> Unit) -M[]> Unit -S[l]> Tuple Unit Unit
        = \uId u2 -> Tuple [Unit] [Unit] (uId Unit) u2;

        main : Two -M[]> L
        = \t ->
        case t of
        | Left l -> l
        | Right r ->
        let R u1 u2 = r in
        let Unit = u1 in
        let uId = id [Unit] in
        let tup = buildUTup ['uId] &uId u2 in
        drop uId in
        let Tuple u3 u4 = tup in
        let Unit = id [Unit] u3 in
        let Unit = u4 in
        L;
        |]
    -- TODO: tests for including functions and function references inside closure environments.
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

        main : Unit -M[]> Two
        = \arg ->
        let Unit = arg in
        let tup = Tuple [L] [R] L (R Unit Unit) in
        let destroyL = \(l:L) -> let L = l in Unit in
        let v = Right (extractRight ['destroyL] [L] [R] &destroyL tup) in
        drop destroyL in v;
        |]
