{-# LANGUAGE BlockArguments, OverloadedStrings, QuasiQuotes #-}
module Rll.TypeCheckSpec where

import Test.Hspec
import qualified Data.Text as T
import qualified Text.Megaparsec as M

import QuoteTxt
import qualified Rll.Parser as RP
import Rll.TypeCheck
import Rll.Ast
import Rll.TypeError (prettyPrintError, TyErr(..))
import Rll.Context

processFile :: T.Text -> Either (M.ParseErrorBundle T.Text RP.RllParseError) (Tc ())
processFile text = mapM_ processDecl <$> M.parse RP.fileDecls "test.rll" text

baseCtx :: Ctx
baseCtx = case runTc emptyCtx fileTc of
  Left err -> error $ show err
  Right (_,ctx) -> ctx
  where fileTc = case processFile file of
          Left err -> error $ M.errorBundlePretty err
          Right v -> v
        file = [txt|
struct Unit {}
struct Int {}
struct Str {}
struct Pair { Int Str }
enum Sum = Left Int | Right Str;
enum Bool = True | False;

consInt : Int -M[]> Unit
= \x -> let Int = x in Unit;

consStr : Str -M[]> Unit
= \x -> let Str = x in Unit;

consPair : Pair -M[]> Unit
= \p -> let Pair i s = p in
let Int = i in let Str = s in Unit;

consSum : Sum -M[]> Unit
= \s -> case s of
| Left i -> let Int = i in Unit
| Right s -> let Str = s in Unit;
|]

buildChecker :: (Tm -> Ty -> Expectation) -> T.Text -> T.Text -> Expectation
buildChecker cmp tmTxt tyTxt = do
  termMay <- runP (RP.tm <* M.eof) tmTxt
  typMay <- runP (RP.ty <* M.eof) tyTxt
  case (termMay, typMay) of
    (Just tm, Just ty) -> cmp tm ty
    _ -> pure ()
  where
    runP :: RP.Parser a -> T.Text -> IO (Maybe a)
    runP p txt = case M.parse (p <* M.eof) "test.rll" txt of
      Right v -> pure $ Just v
      Left err -> do
        expectationFailure $ M.errorBundlePretty err
        pure Nothing

synthTo :: T.Text -> T.Text -> Expectation
synthTo tmTxt tyTxt = buildChecker f tmTxt tyTxt where
  f tm ty = case evalTc baseCtx (synth tm) of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError tmTxt err
    Right ty' -> ty `shouldBe` ty

checkTo :: T.Text -> T.Text -> Expectation
checkTo tmTxt tyTxt = buildChecker f tmTxt tyTxt where
  f tm ty = case evalTc baseCtx (check ty tm) of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError tmTxt err
    Right _ -> pure ()

mkTest :: Ctx -> T.Text -> Expectation
mkTest ctx txt = case processFile txt of
  Left err -> expectationFailure $ M.errorBundlePretty err
  Right tc -> case evalTc ctx tc of
    Left err -> expectationFailure $ T.unpack $ prettyPrintError txt err
    Right _ -> pure ()

rawTest = mkTest emptyCtx
baseTest = mkTest baseCtx

mkFailTest :: Ctx -> TyErr -> T.Text -> Expectation
mkFailTest ctx err txt = case processFile txt of
  Left err -> expectationFailure $ M.errorBundlePretty err
  Right tc -> case evalTc ctx tc of
    Left err' -> err' `shouldBe` err
    Right _ -> expectationFailure "Expected to fail."

baseFailTest = mkFailTest baseCtx

es :: Span
es = Span "test.rll" 1 1 1 1

tyCon v = TyCon (Var v) es
refTy v ty = RefTy (LtOf (Var v) es) ty es

spec :: Spec
spec = do
  -- describe "varsBorrowedIn" do
  --   it "can derive a list of borrowed variables" do
  --     let ctx = Ctx
  --     varsBorrowedIn
  describe "type checking" do
    it "can type check using pair" do
      baseTest [txt|
        val : Pair
        = Pair Int Str;
        |]
    it "can borrow and drop" do
      baseTest [txt|
        test : Unit
        = let a = Unit in let b = &a in drop b in a;
        |]
    it "can check a case of" do
      baseTest [txt|
        test : Unit =
        case Left Int of
        | Left d -> let Int = d in Unit
        | Right d -> let Str = d in Unit;
        |]
    it "checks that using a reference variable consumes it" do
      baseTest [txt|
        test : Unit =
        let a = Left Int in
        let Unit =
          (let d = &a in
          case d of
          | Left b -> drop b in Unit
          | Right c -> drop c in Unit) in
        case a of
        | Left d -> let Int = d in Unit
        | Right e -> let Str = e in Unit;
        |]
    it "can use module functions" do
      baseTest [txt|
        t1 : Unit
        = consInt Int;

        t2 : Unit
        = consStr Str;
        |]
    it "can catch an incorrect struct" do
      baseFailTest (ExpectedButInferred (tyCon "Unit") (tyCon "Int") es) [txt|
        test : Unit = Int;
        |]
    it "can check type application" do
      baseTest [txt|
        id : forall M [] t : Type . t -S[]> t
        = ^ t : Type -> \v -> v;
        test1 : Unit -S[]> Unit
        = id [ Unit ];

        test2 : Unit
        = (id [ Unit ]) Unit;

        test3 : Unit
        = id [ Unit ] Unit;
        |]

    it "can decompose a reference product" do
      baseTest [txt|
        consumeISR :
          forall M [] l1 : Lifetime .
          forall S [] l2 : Lifetime .
          &l1 Int -S[]> &l2 Str -S[]> Unit
        = ^ l1 : Lifetime -> ^ l2 : Lifetime -> \ir -> \sr ->
        drop ir in drop sr in Unit;

        test : Unit
        = let a = Pair Int Str in
        let Pair i s = &a in
        let Unit = consumeISR ['a] ['a] i s in
        let Pair i s = a in
        let Int = i in let Str = s in Unit;

        |]

    it "can catch using a borrowed variable" do
      let err = CannotUseBorrowedVar (Var "a") [Var "b"] es
      baseFailTest err [txt|
        test : Pair
        = let a = Pair Int Str in
        let b = &a in a;
        |]

    it "can synthesize a multiple use function type" do
      "\\ a : Unit -> a" `synthTo` "Unit -M[]> Unit"

    it "can synth and check a single use function type" do
      let f = [txt|let a = Int in (\b : Unit -> let Int = a in b) |]
          fTy = "Unit -S[]> Unit"
      f `synthTo` fTy
      f `checkTo` fTy

    it "can catch using the wrong constructor in let-struct" do
      baseFailTest (WrongConstructor (Var "Unit") "Int" (Var "Int") es) [txt|
        test : Int -M[]> Unit -S[]> Unit
        = \a -> \b : Unit -> let Unit = a in b;
        |]

    it "can infer a function type that captures references" do
      baseTest [txt|
        test : Unit
        = let a = Left Int in let Unit =
        (\b : Unit -> case &a of
          | Left i -> drop i in b
          | Right s -> drop s in b) Unit in
        consSum a;
        |]

    it "can check a function type that captures references" do
      baseTest [txt|
        test : Unit
        = let a = Left Int in let Unit =
        ((\b : Unit -> case &a of
          | Left i -> drop i in b
          | Right s -> drop s in b)
          : Unit -M['a]> Unit) Unit in
        consSum a;
        |]

    it "can coerce a multi-use function to be single use" do
      baseTest [txt|
        test : Unit
        = let f = ((\b:Unit -> b) : Unit -S[]> Unit) in
        f Unit;
        |]

    it "can catch a multi-use function consuming a variable" do
      baseFailTest (MultiFnCannotConsume [Var "a"] es)[txt|
         test : Unit -M[]> Unit
         = let a = Int in \x -> let Int = a in x;
         |]

    it "can catch a variable escaping the scope" do
      baseFailTest (VarsEscapingScope [Var "a"] es) [txt|
         test : Unit -M[]> Unit
         = \x -> let a = Int in x;
         |]

    it "can check simple recursive functions" do
      baseTest [txt|
         test : Unit -M[]> Unit
         = fun f (x) drop f in x;

         test2 : Unit -M[]> Unit -M[]> Unit
         = fun f1 (x) drop f1 in
         let Unit = x in
         fun f2 (y) drop f2 in y;
         |]

    it "can catch a recursive function being single use" do
      baseFailTest (RecFunIsNotSingle es es) [txt|
        test : Unit -S[]> Unit
        = fun f1 (x) x;
        |]

    it "can check complex recursive functions" do
      baseTest [txt|
        enum Nat = Succ Nat | Zero;

        double : forall M [] l : Lifetime. &l Nat -M[]> Nat
        = ^ l : Lifetime -> fun f (x) case x of
        | Zero -> drop f in Zero
        | Succ n -> Succ (Succ (f n));

        add : forall M [] l : Lifetime. &l Nat -M[]> Nat -S[l]> Nat
        = ^ l : Lifetime -> fun f (natRef) \nat ->
        case natRef of
        | Succ n -> f n (Succ nat)
        | Zero -> drop f in nat;
        |]

    it "can check usage of reference copy" do
      baseTest [txt|
        test : Int
        = let a = Int in
        let b = &a in
        let c = copy b in
        drop b in
        drop c in
        a;
        |]

    it "can prevent copying a non-reference" do
      let ty = tyCon "Int"
      baseFailTest (CannotCopyNonRef ty es) [txt|
        test : Int
        = let a = Int in
        let b = copy a in
        a;
        |]

    it "can prevent taking reference of a reference" do
      let ty = refTy "a" (tyCon "Int")
      baseFailTest (CannotRefOfRef ty es) [txt|
        test : Int
        = let a = Int in
        let b = &a in
        let c = &b in
        drop b in
        drop c in
        a;
        |]

    it "can catch splitting on a non-enum" do
      baseFailTest (TypeIsNotEnum (tyCon "Int") es) [txt|
        test : Unit
        = let a = Int in
        case a of
        | True -> Unit
        | False -> Unit;
        |]

      baseFailTest (TypeIsNotEnum (tyCon "Int") es) [txt|
        test : Unit
        = case Int of
        | True -> Unit
        | False -> Unit;
        |]

    it "can catch destructuring a non-struct" do
      baseFailTest (TypeIsNotStruct (tyCon "Sum") es) [txt|
        test : Unit
        = let Pair x y = Left Int in
        let Int = x in
        conStr y;
        |]

    -- it "" do
    --   baseTest [txt|
    --     test : Unit = Unit
    --     |]

    -- TODO make sure I don't have any problems with type substitution
    -- capturing a free variable in lifetimes.

    -- TODO check copy
      -- baseTest [txt|
      --   test : Unit = Unit
      --   |]
