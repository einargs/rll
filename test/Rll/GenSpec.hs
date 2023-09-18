{-# LANGUAGE QuasiQuotes #-}
module Rll.GenSpec where

import QuoteTxt
import qualified Rll.Parser as RP
import Rll.SpecIR (SpecResult(..))
import Rll.TypeCheck (typeCheckFile)
import Rll.TypeError (prettyPrintError)
import Rll.TcMonad (runTc)
import Rll.Spec (specModule)
import Rll.Context
import Rll.GenLLVM
import Rll.OrchTypes qualified as OT
import Rll.Orchestra (jitModule)

import LLVM.Context qualified as L
import LLVM.Module qualified as L
import LLVM.AST qualified as A
import LLVM.AST.DataLayout qualified as A

import Data.Int (Int64)
import Data.Text (Text)
import Data.Text qualified as T
import Text.Megaparsec qualified as MP
import Data.ByteString.Char8 qualified as BS
import Test.Hspec

parseFile' :: Text -> IO (Maybe SpecResult)
parseFile' txt = case MP.parse RP.fileDecls "test.rll" txt of
  Left err -> exFail $ MP.errorBundlePretty err
  Right decls ->
    case runTc emptyCtx $ typeCheckFile decls of
      Left err -> exFail $ T.unpack $ prettyPrintError txt err
      Right (tcResult, _) ->
        case specModule tcResult of
          Left err -> exFail $ "Specialization error: " <> show err
          Right specResult -> pure $ Just specResult
  where
  exFail msg = do
    expectationFailure msg
    pure Nothing

willGen :: Text -> Expectation
willGen txt = do
  mbSpecDecls <- parseFile' txt
  case mbSpecDecls of
    Nothing -> pure ()
    Just specResult -> L.withContext \ctx -> do
      let layout = A.defaultDataLayout A.LittleEndian
      result <- runGen specResult ctx layout
      case result of
        Left err -> expectationFailure $ "Gen error: " <> show err
        Right defs -> do
          let mod = A.Module "test" "test.rll" (Just layout) Nothing defs
          -- print $ "defs: " <> show defs
          llvm <- L.withModuleFromAST ctx mod L.moduleLLVMAssembly
          BS.putStrLn llvm

jit :: HasCallStack => Int64 -> Int64 -> Text -> Expectation
jit input output source = do
  let src = OT.RllSrcModule
            { fileName = "test.rll"
            , moduleName = "test"
            , moduleSrc = source
            }
  jitModule src \case
    Left err -> expectationFailure $ T.unpack $ OT.prettyPrintError src err
    Right fun -> do
      val <- fun input
      val `shouldBe` output

spec :: Spec
spec = do
  describe "generate llvm" do
    it "generates an id function" do
      jit 1 1 [txt|
        struct U2 {}
        struct Unit {}

        thing : U2 -M[]> U2
        = \ u -> u;

        other : Unit -M[]> Unit
        = \u -> u;

        main : I64 -M[]> I64
        = \i ->
        let U2 = thing U2 in
        let Unit = other Unit in i;
        |]
    it "simple bool" do
      jit 1 2 [txt|
        enum Bool = True | False;

        invert : Bool -M[]> Bool
        = \b -> case b of
        | True -> False
        | False -> True;

        main : I64 -M[]> I64
        = \i1 ->
        let i2 = case invert False of
        | True -> addI64 i1 1
        | False -> addI64 i1 0 in
        case True of
        | True -> addI64 i2 4
        | False -> addI64 i2 2;
        |]
    it "uses a polymorphic type as an argument to a polymorphic function" do
      jit 1 2 [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        center : Two -M[]> L
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

        main : I64 -M[]> I64
        = \i ->
        let L = center (Right (R Unit Unit)) in
        addI64 1 i;
        |]
    it "uses a multi argument function" do
      jit 3 4 [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : Unit -M[]> Unit -S[]> Tuple Unit Unit
        = \u1 u2 -> Tuple [Unit] [Unit] u1 u2;

        center : Two -M[]> L
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

        main : I64 -M[]> I64
        = \i ->
        let L = center (Right (R Unit Unit)) in
        addI64 1 i;
        |]
    it "takes a function as an argument" do
      jit 5 6 [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : (Unit -M[]> Unit) -M[]> Unit -S[]> Tuple Unit Unit
        = \uId u2 -> Tuple [Unit] [Unit] (uId Unit) u2;

        center : Two -M[]> L
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

        main : I64 -M[]> I64
        = \i ->
        let L = center (Right (R Unit Unit)) in
        addI64 i 1;
        |]
    it "takes a reference to a function as an argument" do
      jit 7 8 [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }
        enum Two = Left L | Right R;

        id : forall M [] a:Type. a -M[]> a
        = \v -> v;

        buildUTup : forall M [] l:Lifetime. &l (Unit -M[]> Unit) -M[]> Unit -S[l]> Tuple Unit Unit
        = \uId u2 -> Tuple [Unit] [Unit] (uId Unit) u2;

        center : Two -M[]> L
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

        main : I64 -M[]> I64
        = \i ->
        let L = center (Right (R Unit Unit)) in
        addI64 i 1;
        |]
    -- TODO: tests for including functions and function references inside closure environments.
    it "can run a complex use case" do
      jit 9 10 [txt|
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

        center : Unit -M[]> Two
        = \arg ->
        let Unit = arg in
        let tup = Tuple [L] [R] L (R Unit Unit) in
        let destroyL = \(l:L) -> let L = l in Unit in
        let v = Right (extractRight ['destroyL] [L] [R] &destroyL tup) in
        drop destroyL in v;

        main : I64 -M[]> I64
        = \i ->
        case center Unit of
        | Left l -> let L = l in i
        | Right r -> let R u1 u2 = r in
        let Unit = u1 in let Unit = u2 in
        addI64 i 1;
        |]
    it "can double a 64 bit integer using the JIT" do
      jit 1 2 [txt|
        main : I64 -M[]> I64
        = \i -> addI64 (copy i) i;
        |]
