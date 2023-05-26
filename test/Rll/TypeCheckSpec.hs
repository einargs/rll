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
          &l1 Int -S[]> &l2 Str -S[l1]> Unit
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

    it "can check complex multi-argument functions with polymorphism" do
      baseTest [txt|
        copyInt1 :
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = ^ \r -> drop r in Int;

        copyInt2 :
          Unit -M[]>
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = \x -> let Unit = x in ^ \r -> drop r in Int;

        copyInt2e :
          Unit -M[]>
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = \x -> let Unit = x in ^ l : Lifetime -> \r -> drop r in Int;

        copyInt3 :
          forall M [] l1 : Lifetime.
          &l1 Unit -M[]>
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = ^ \x -> drop x in ^ \r -> drop r in Int;

        copyInt3e :
          forall M [] l1 : Lifetime.
          &l1 Unit -M[]>
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = ^l1:Lifetime -> \x -> drop x in ^ l : Lifetime -> \r -> drop r in Int;

        test : Unit
        = let i = Int in
        let u = Unit in
        let Int = copyInt1 ['i] &i in
        let Int = copyInt3e ['u] &u ['i] &i in
        let Unit = u in
        let Int = i in
        Unit;
        |]

    it "can check complex recursive functions" do
      baseTest [txt|
        enum Nat = Succ Nat | Zero;

        double : forall M [] l : Lifetime. &l Nat -M[]> Nat
        = let wrap = (fun w (u)
        let Unit = u in
        let f = w Unit in
        ^ l : Lifetime -> \ x -> case copy x of
        | Zero -> Zero
        | Succ n -> Succ (Succ (&f [l] n)))
          : Unit -M[]> forall M [] l : Lifetime. &l Nat -M[]> Nat
        in wrap Unit;

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

    it "can catch an unbound type variable" do
      baseFailTest (UnknownTypeVar "a" es) [txt|
        test : &a Int -M[]> Int
        = \r-> drop r in Int;
        |]

    it "can catch an unknown data type" do
      baseFailTest (UnknownDataType (Var "Toxic") es) [txt|
        test : Toxic -M[]> Toxic
        = \t-> t;
        |]

    it "can catch an unbound term variable in a lifetime" do
      baseFailTest (UnknownTermVar (Var "l") es) [txt|
        test : &'l Int -M[]> Unit
        = \r -> drop r in Unit;
        |]

    it "can catch a reference used after being dropped" do
      baseFailTest (RemovedTermVar es es) [txt|
        copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
        = ^ l : Lifetime -> \r -> drop r in Int;

        test : Int -M[]> Int
        = \a -> let b = &a in
        drop b in
        let Int = copyInt ['a] b in
        a;
        |]

    it "can catch applying a term argument instead of a type argument" do
      baseFailTest (TyIsNotFun (tyCon "Int") es) [txt|
        test : Unit -M[]> Unit
        = \a -> let Int = Int Str in a;
        |]

    it "can catch using an already used variable" do
      baseFailTest (RemovedTermVar es es) [txt|
        test : Unit -M[]> Unit
        = \a-> let Unit = a in a;
        |]

    it "can check applying two different type variables" do
      baseTest [txt|
        consume2Ref :
          forall M [] l1 :Lifetime. forall M[] l2 : Lifetime.
          &l1 Int -M[]> &l2 Str -S[l1]> Unit
        = ^ ^ \ir -> \sr ->
        drop ir in drop sr in
        Unit;

        test : Unit -M[]> Unit
        = \a-> let i = Int in
        let s = Str in
        let Unit = ((((consume2Ref ['i])
        : forall M [] l2 : Lifetime. &'i Int -M[]> &l2 Str -S['i]> Unit)
        ['s]) : &'i Int -M[]> &'s Str -S['i]> Unit)
          &i &s in
        let Int = i in let Str = s in a;
        |]

    it "can avoid free variable capture in type substitution" do
      baseTest [txt|
        id : forall M [] t : Type. t -M[]> t
        = ^ \a -> a;

        test : forall M [] t : Type. t -M[]> t
        = ^ t : Type -> \a ->
        let b = id [&'a t] &a in
        drop b in a;
        |]

    it "can use a local multi-use function through references" do
      baseTest [txt|
        test : Unit
        = let f = \a:Unit -> a in
        let Unit = &f Unit in
        let Unit = &f Unit in
        drop f in
        Unit;
        |]


    it "can check directly borrowing an external variable" do
      baseTest [txt|
        copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
        = ^ \r -> drop r in Int;

        test : Unit
        = let i = Int in
        let f = ((\u ->
          let Unit = u in
          copyInt ['i] &i)
          : Unit -M['i]> Int) in
        let i1 = &f Unit in
        let i2 = &f Unit in
        let Int = i1 in let Int = i2 in
        drop f in
        let Int = i in
        Unit;
        |]

    it "can check directly copying an external variable" do
      baseTest [txt|
        copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
        = ^ \r -> drop r in Int;

        test : Unit
        = let i = Int in
        let ir = &i in
        let f = ((\u ->
          let Unit = u in
          copyInt ['i] copy ir)
          : Unit -M['i]> Int) in
        let Int = &f Unit in
        let Int = &f Unit in
        drop ir in
        drop f in
        let Int = i in
        Unit;
        |]

    it "can catch an incorrect borrow list" do
      let lt s = LtOf (Var s) es
          ty1 = LtJoin [lt "i", lt "s"] es
          list = [lt "i"]
      baseFailTest (IncorrectBorrowedVars ty1 list es) [txt|
        copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
        = ^ \r -> drop r in Int;

        test : Unit
        = let i = Int in
        let s = Str in
        let ir = &i in
        let f = ((\u ->
          let Unit = u in
          copyInt ['i] copy ir)
          : Unit -M['i, 's]> Int) in
        drop ir in
        drop f in
        let Int = i in
        Unit;
        |]

    it "Are borrow lists in returned functions checked" do
      -- TODO: once this checks rewrite it to cause an error I can make sure works.
      baseTest [txt|
        copyInt : forall M [] l : Lifetime. &l Int -M[]> Int
        = ^ \r -> drop r in Int;

        mkCopier : forall M [] l : Lifetime.
          &l Int -M[]> Unit -M[l]> Int
        = ^l:Lifetime -> \r->
        let f = (\u:Unit -> let Unit = u in copyInt [l] (copy r)) in
        drop r in f;

        test : Unit -M[]> Unit
        = \a ->
        let i = Int in
        let cp = mkCopier ['i] &i in
        let i1 = &cp Unit in
        let i2 = &cp Unit in
        let Int = i1 in let Int = i2 in
        drop cp in
        let Int = i in
        a;
        |]

    -- TODO it "properly maintains borrow counts when returning univ and function types."
    it "shifts type variable indices for term variable types" do
      -- Basically we're checking to make sure that if I have a type variable with index 0
      -- in a variable's type, and then introduce a type binder, that variable is shifted
      -- to account for the change.
      baseTest [txt|
        f : forall M [] t : Type.
          t -M[]> forall S [] l : Lifetime.
          &l t -S[]> t
        = ^ t : Type -> \v -> ^ l : Lifetime ->
        \ r -> drop r in v;

        test : Unit -M[]> Unit
        = \ a ->
        let b = Unit in
        let c = f [Unit] a ['b] &b in
        let Unit = b in c;
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
