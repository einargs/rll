{-# LANGUAGE BlockArguments, OverloadedStrings, QuasiQuotes #-}
module Rll.TypeCheckSpec where

import Rll.Ast
import Rll.TypeError (TyErr(..))

import Test.Hspec

import Rll.AstUtil
import Rll.TcSpecUtil

spec :: Spec
spec = parallel do
  describe "type checking" do
    it "Standard context parses" do
      rawTest stdFile
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
        = \ [t : Type] v -> v;
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
        = \ [l1 : Lifetime] [l2 : Lifetime] ir sr ->
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
      "\\ (a : Unit) -> a" `synthTo` "Unit -M[]> Unit"

    it "can synth and check a single use function type" do
      let f = [txt|let a = Int in (\(b : Unit) -> let Int = a in b) |]
          fTy = "Unit -S[]> Unit"
      f `synthTo` fTy
      f `checkTo` fTy

    it "can catch using the wrong constructor in let-struct" do
      baseFailTest (WrongConstructor (Var "Unit") "Int" (Var "Int") es) [txt|
        test : Int -M[]> Unit -S[]> Unit
        = \a (b : Unit) -> let Unit = a in b;
        |]

    it "can infer a function type that captures references" do
      baseTest [txt|
        test : Unit
        = let a = Left Int in let Unit =
        (\(b : Unit) -> case &a of
          | Left i -> drop i in b
          | Right s -> drop s in b) Unit in
        consSum a;
        |]

    it "can check a function type that captures references" do
      baseTest [txt|
        test : Unit
        = let a = Left Int in let Unit =
        ((\(b : Unit) -> case &a of
          | Left i -> drop i in b
          | Right s -> drop s in b)
          : Unit -M['a]> Unit) Unit in
        consSum a;
        |]

    it "can coerce a multi-use function to be single use" do
      baseTest [txt|
        test : Unit
        = let f = ((\(b:Unit) -> b) : Unit -S[]> Unit) in
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
         = rec f \ x -> x;

         test2 : Unit -M[]> Unit -M[]> Unit
         = rec f1 \ x ->
         let Unit = x in
         rec f2 \ y -> y;
         |]

    it "can catch a recursive function being single use" do
      baseFailTest (CannotFixSingle es es) [txt|
        test : Unit -S[]> Unit
        = rec f \ x -> x;
        |]
    it "can catch a recursive polymorphic function being single use" do
      baseFailTest (CannotFixSingle es es) [txt|
        test : forall S [] l : Lifetime. &l Unit -S[]> Unit
        = rec f \ x -> drop x in Unit;
        |]

    it "can check complex multi-argument functions with polymorphism" do
      baseTest [txt|
        copyInt1 :
          forall M [] l : Lifetime.
          &l Int -M[]> Int
        = \r -> drop r in Int;

        copyInt2 :
          forall M [] l : Lifetime.
          Unit -M[]>
          &l Int -M[]> Int
        = \x -> let Unit = x in \r -> drop r in Int;

        copyInt2e :
          forall M [] l : Lifetime.
          Unit -M[]>
          &l Int -M[]> Int
        = \[l:Lifetime] x -> let Unit = x in \r -> drop r in Int;

        copyInt3 :
          forall M [] l1 : Lifetime.
          forall M [] l : Lifetime.
          &l1 Unit -M[]>
          &l Int -M[]> Int
        = \x -> drop x in \r -> drop r in Int;

        copyInt3e :
          forall M [] l1 : Lifetime.
          forall M [] l : Lifetime.
          &l1 Unit -M[]>
          &l Int -M[]> Int
        = \[l1:Lifetime] [l:Lifetime] x -> drop x in \r -> drop r in Int;

        test : Unit
        = let i = Int in
        let u = Unit in
        let Int = copyInt1 ['i] &i in
        let Int = copyInt3e ['u] ['i] &u &i in
        let Unit = u in
        let Int = i in
        Unit;
        |]

    it "can check complex recursive functions" do
      baseTest [txt|
        enum Nat = Succ Nat | Zero;

        double : forall M [] l : Lifetime. &l Nat -M[]> Nat
        = rec f \ [l : Lifetime] x ->
        case x of
        | Zero -> Zero
        | Succ n -> Succ (Succ (copy f [l] n));

        add : forall M [] l : Lifetime. &l Nat -M[]> Nat -S[l]> Nat
        = rec f \ [l : Lifetime] natRef nat ->
        case natRef of
        | Succ n -> copy f [l] n (Succ nat)
        | Zero -> nat;
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
      let ty = refVar "a" (tyCon "Int")
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
      baseFailTest (UnknownTypeVar (MkTyVar "a" 0) es) [txt|
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
      baseFailTest (RemovedTermVar (Var "b") es es) [txt|
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
      baseFailTest (RemovedTermVar (Var "a") es es) [txt|
        test : Unit -M[]> Unit
        = \a-> let Unit = a in a;
        |]

    it "can check applying two different type variables" do
      baseTest [txt|
        consume2Ref :
          forall M [] l1 :Lifetime. forall M[] l2 : Lifetime.
          &l1 Int -M[]> &l2 Str -S[l1]> Unit
        = \ir sr ->
        drop ir in drop sr in
        Unit;

        test : Unit -M[]> Unit
        = \a-> let i = Int in
        let s = Str in
        let Unit = consume2Ref ['i] ['s] &i &s in
        let Unit = ((consume2Ref ['i] ['s]
        ) : &'i Int -M[]> &'s Str -S['i]> Unit)
          &i &s in
        let Int = i in let Str = s in a;
        |]

    it "can avoid free variable capture in type substitution" do
      baseTest [txt|
        id : forall M [] t : Type. t -M[]> t
        = \a -> a;

        test : forall M [] t : Type. t -M[]> t
        = \ [t : Type] a ->
        let b = id [&'a t] &a in
        drop b in a;
        |]

    it "can use a local multi-use function through references" do
      baseTest [txt|
        test : Unit
        = let f = \(a:Unit) -> a in
        let Unit = &f Unit in
        let Unit = &f Unit in
        drop f in
        Unit;
        |]


    it "can check directly borrowing an external variable" do
      baseTest [txt|
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
      let ty1 = ltJoin [ltOf "i", ltOf "s"]
          list = [ltOf "i"]
      baseFailTest (IncorrectBorrowedVars ty1 list es) [txt|
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
        mkCopier : forall M [] l : Lifetime.
          &l Int -M[]> Unit -M[l]> Int
        = \[l:Lifetime] r->
        let f = (\(u:Unit) -> let Unit = u in copyInt [l] (copy r)) in
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

    it "shifts type variable indices for term variable types" do
      baseTest [txt|
        f : forall M [] t : Type.
          forall S [] l : Lifetime.
          t -M[]> &l t -S[]> t
        = \ [t : Type] [l : Lifetime] v ->
        let fr = \[l2:Lifetime] [t2: Type] (r: &l2 t) -> drop r in v in
        fr [l] [t];

        test : Unit -M[]> Unit
        = \ a ->
        let b = Unit in
        let c = f [Unit] ['b] a &b in
        let Unit = b in c;
        |]

    it "maintains borrow counts when returning function types" do
      baseTest [txt|
        other : forall S [] l1 : Lifetime.
          forall S [] l2 : Lifetime.
          forall S [] t : Type.
          &l1 Unit -S[]> &l2 Unit -S[l1]>
          t -S[l1, l2]> t
        = \ [l1 : Lifetime] [l2 : Lifetime] [t:Type] r1 r2 y ->
        drop r1 in drop r2 in y;

        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let partial = other ['u1] ['u2] [Int] &u1 in
        let Int = partial &u2 Int in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]

    it "can capture references to a variable outside a closure" do
      baseTest [txt|
        test : Int
        = let i = Int in
        let f = ((\x ->
          let r = &i in drop r in x)
          : Unit -M['i]> Unit) in
        let Unit = &f Unit in
        let Unit = &f Unit in
        drop f in i;
        |]

      baseTest [txt|
        test : Int
        = let i = Int in
        let f = (\(x:Unit) ->
          let r = &i in drop r in x)
          in
        let Unit = &f Unit in
        let Unit = &f Unit in
        drop f in i;
        |]

    it "can capture references to a variable outside a two argument closure" do
      baseTest [txt|
        test : Int
        = let i = Int in
        let f = ((\x y ->
          let Unit = y in
          let r = &i in drop r in x)
          : Unit -M['i]> Unit -S['i]> Unit) in
        let Unit = &f Unit Unit in
        let Unit = &f Unit Unit in
        drop f in i;
        |]

      baseTest [txt|
        test : Int
        = let i = Int in
        let f = (\(x: Unit) (y:Unit) ->
          let Unit = y in
          let r = &i in drop r in x) in
        let Unit = &f Unit Unit in
        let Unit = &f Unit Unit in
        drop f in i;
        |]

    it "can copy references to a variable outside a two argument closure" do
      baseTest [txt|
        test : Int
        = let i = Int in
        let ir = &i in
        let f = ((\x y ->
          let Unit = y in
          let r = copy ir in drop r in x)
          : Unit -M['i]> Unit -S['i]> Unit) in
        let Unit = &f Unit Unit in
        let Unit = &f Unit Unit in
        drop ir in
        drop f in i;
        |]

      baseTest [txt|
        test : Int
        = let i = Int in
        let ir = &i in
        let f = (\(x:Unit) (y:Unit) ->
          let Unit = y in
          let r = copy ir in drop r in x) in
        let Unit = &f Unit Unit in
        let Unit = &f Unit Unit in
        drop ir in
        drop f in i;
        |]

    it "can copy external references in a polymorphic closure" do
      baseTest [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let r1 = &u1 in let r2 = &u2 in
        let other =
          ((\y ->
            let c1 = copy r1 in let c2 = copy r2 in
            drop c1 in drop c2 in y)
            : forall S ['u1, 'u2] t : Type.
            t -S['u1, 'u2]> t) in
        let final = other [Int] in
        let Int = final Int in
        drop r1 in drop r2 in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]

      baseTest [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let r1 = &u1 in let r2 = &u2 in
        let other =
          (\[t:Type] (y:t) ->
            let c1 = copy r1 in let c2 = copy r2 in
            drop c1 in drop c2 in y) in
        let final = other [Int] in
        let Int = final Int in
        drop r1 in drop r2 in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]


    it "can return a captured reference in a closure" do
      baseTest [txt|
        test : Unit
        = let u = Unit in
        let mkRef = (\(x:Unit) (y:Unit) (z:Unit) ->
          let Unit = z in
          let Unit = x in
          let Unit = y in &u) in
        let ur = mkRef Unit Unit Unit in
        drop ur in
        u;
        |]

      baseTest [txt|
        test : Unit
        = let u = Unit in
        let mkRef = (\x y z ->
          let Unit = z in
          let Unit = x in
          let Unit = y in &u)
          : Unit -M['u]> Unit -S['u]> Unit -S['u]> &'u Unit
        in
        let ur = mkRef Unit Unit Unit in
        drop ur in
        u;
        |]

    it "correctly drops multi-use functions" do
      baseFailTest (RemovedTermVar (Var "f") es es) [txt|
        test : Unit
        = let f = (\(x:Unit) -> x) in
        let Unit = f Unit in
        drop f in
        Unit;
        |]

      baseTest [txt|
        test : Unit
        = let f = (\(x:Unit) -> x) in
        let Unit = &f Unit in
        drop f in
        Unit;
        |]

    it "can take a function that captures references as an argument" do
      -- TODO write a version that does checked lambdas
      baseTest [txt|
        test : Unit
        = let u = Unit in
        let argF = (\x -> let r = &u in drop r in x)
          : Unit -M['u]> Unit in
        let argF2 = (\x -> let r = &u in drop r in x)
          : Unit -M['u]> Unit in
        let useArgF = (\f -> f Unit)
          : (Unit -M['u]> Unit) -M[]> Unit in
        let holdArgF = (\f x ->
          let Unit = x in f Unit)
          : (Unit -M['u]> Unit) -M[]> Unit -S['u]> Unit in
        let Unit = &argF Unit in
        let Unit = useArgF argF in
        let hold = holdArgF argF2 in
        let Unit = hold Unit in
        u;
        |]

    it "can take a function that captures references as an argument in synthesized lambda" do
      baseTest [txt|
        test : Unit
        = let u = Unit in
        let argF = (\(x:Unit) -> let r = &u in drop r in x) in
        let argF2 = (\(x:Unit) -> let r = &u in drop r in x) in
        let useArgF = \(f:Unit -M['u]> Unit) -> f Unit in
        let holdArgF = \(f:Unit -M['u]> Unit) (x:Unit) ->
          let Unit = x in f Unit in
        let Unit = &argF Unit in
        let Unit = useArgF argF in
        let hold = holdArgF argF2 in
        let Unit = hold Unit in
        u;
        |]

    -- TODO: it "can capture a reference to a multi-use function" do

    it "can return a captured reference in a struct" do
      -- synthesized
      baseTest [txt|
        struct Holder (a:Type) { a }

        test : Unit
        = let u = Unit in
        let mkRef = (\(x:Unit) (y:Unit) (z:Unit) ->
          let Unit = z in
          let Unit = x in
          let ur = &u in
          let Unit = y in Holder [&'u Unit] ur) in
        let Holder ur = mkRef Unit Unit Unit in
        drop ur in
        u;
        |]

      -- checked
      baseTest [txt|
        struct Holder (a:Type) { a }

        test : Unit
        = let u = Unit in
        let mkRef = (\x y z ->
          let Unit = z in
          let Unit = x in
          let Unit = y in Holder [&'u Unit] &u)
          : Unit -M['u]> Unit -S['u]> Unit -S['u]> Holder (&'u Unit) in
        let Holder ur = mkRef Unit Unit Unit in
        drop ur in
        u;
        |]

    it "move an external reference from one lambda into a nested lambda" do
      -- note that dropping `c1` is the same as moving it.
      baseTest [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let other = ((\u -> let c1 = &u1 in
          \y -> let Unit = u in
            let c2 = &u2 in
            drop c1 in drop c2 in y)
          : forall M ['u1, 'u2] t : Type.
            Unit -M['u1, 'u2]> t -S['u1,'u2]> t) in
        let Int = other [Int] Unit Int in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]

      baseTest [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let other = ((\u -> let c1 = &u1 in
          \y -> let c1c = c1 in
            let Unit = u in
            let c2 = &u2 in
            drop c1c in drop c2 in y)
          : forall M ['u1, 'u2] t : Type.
            Unit -M['u1, 'u2]> t -S['u1,'u2]> t) in
        let Int = other [Int] Unit Int in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]

      baseFailTest (VarsEscapingScope [Var "c1"] es) [txt|
        test : Unit
        = let u1 = Unit in
        let u2 = Unit in
        let other = ((\u -> let c1 = &u1 in
          \y -> let Unit = u in
            let c2 = &u2 in
            drop c2 in y)
          : forall M ['u1, 'u2] t : Type.
            Unit -M['u1, 'u2]> t -S['u2]> t) in
        let Int = other [Int] Unit Int in
        let Unit = u1 in
        let Unit = u2 in
        Unit;
        |]

    it "prevents passing a borrow unit to a closure that references it" do
      -- Current limitations mean that we can't accurately diagnose that `f`
      -- is borrowing `u1`. We decrement the `lts` after checking `u1`,
      -- but the variable deletion happens earlier. See Eventual Polish
      -- in `TODO.md` for more information.
      baseFailTest (CannotUseBorrowedVar (Var "u1") [] es) [txt|
        test : Unit
        = let u1 = Unit in
        let f = \(u:Unit) -> let ur = &u1 in
          drop ur in u in
        let Unit = f u1 in
        Unit;
        |]

      baseFailTest (CannotUseBorrowedVar (Var "u1") [] es) [txt|
        struct Holder (a : Lifetime) { (&a Unit) }

        test : Unit
        = let u1 = Unit in
        let f = \[l:Lifetime] (h:Holder l) (u:Unit) ->
          let Holder ur = h in
          drop ur in u
        in
        let Unit = f ['u1] (Holder ['u1] &u1) u1 in
        Unit;
        |]

      baseTest [txt|
        struct Holder (a : Lifetime) { (&a Unit) }

        test : Unit
        = let u1 = Unit in
        let f = \[l:Lifetime] (h:Holder l) ->
          let Holder ur = h in
          drop ur in \(u:Unit) -> u
        in
        let Unit = f ['u1] (Holder ['u1] &u1) u1 in
        Unit;
        |]

    it "can handle structures with multiple duplicate references" do
      baseTest [txt|
        struct Holder (a : Lifetime) { (&a Unit) (&a Unit) }
        test : Unit
        = let u1 = Unit in
        let f = \(h:Holder 'u1) ->
          let Holder r1 r2 = h in
          drop r1 in drop r2 in
          Unit
        in
        let Unit = f (Holder ['u1] &u1 &u1) in
        u1;
        |]

      baseTest [txt|
        struct Holder (a : Lifetime) { (&a Unit) (&a Unit) Unit }
        test : Unit
        = let u1 = Unit in
        let f = \[l:Lifetime](h:&l (Holder 'u1)) ->
          let Holder r1 r2 r3 = h in
          let r2c = (r2 : &'u1 Unit) in
          let r3c = r3 : &l Unit in
          drop r1 in drop r2c in drop r3c in
          Unit
        in
        let h = Holder ['u1] &u1 &u1 Unit in
        let Unit = f ['h] &h in
        let Holder r1 r2 u3 = h in
        drop r1 in drop r2 in
        let Unit = u3 in u1;
        |]

      baseTest [txt|
        struct Holder (a : Lifetime) { (&a Unit) }
        test : Unit
        = let u1 = Unit in
        let f = \(h:Holder 'u1) ->
          let Holder r1 = h in
          drop r1 in
          Unit
        in
        let Unit = f (Holder ['u1] &u1) in
        u1;
        |]

      baseTest [txt|
        struct Holder (a : Lifetime) { (&a Unit) (&a Unit) }
        test : Unit
        = let u1 = Unit in
        let Unit = (
          let h = Holder ['u1] &u1 &u1 in
          let Holder r1 r2 = h in
          drop r1 in drop r2 in Unit)
        in u1;
        |]

    it "can handle enums with duplicate references" do
      baseTest [txt|
        enum Dub (a : Lifetime)
          = Two (&a Unit) (&a Unit)
          | None;

        test : Unit
        = let u1 = Unit in
        let f = \(d:Dub 'u1) ->
          case d of
          | Two r1 r2 ->
            drop r1 in drop r2 in Unit
          | None -> Unit
        in
        let Unit = f (Two ['u1] &u1 &u1) in
        u1;
        |]
      baseTest [txt|
        enum Dub (a : Lifetime)
          = Two (&a Unit) (&a Unit) Unit
          | None;

        test : Unit
        = let u1 = Unit in
        let f = \[l:Lifetime] (d:&l (Dub 'u1)) ->
          case d of
          | Two r1 r2 r3 ->
            let r2c = (r2 : &'u1 Unit) in
            let r3c = (r3 : &l Unit) in
            drop r1 in drop r2c in drop r3c in Unit
          | None -> Unit
        in
        let e = Two ['u1] &u1 &u1 Unit in
        let Unit = f ['e] &e in
        case e of
        | Two r1 r2 u3 ->
          drop r1 in drop r2 in
          let Unit = u3 in u1
        | None -> u1;
        |]
      baseTest [txt|
        enum Dub (a : Lifetime)
          = Two (&a Unit)
          | None;

        test : Unit
        = let u1 = Unit in
        let f = \(d:Dub 'u1) ->
          case d of
          | Two r1 ->
            drop r1 in Unit
          | None -> Unit
        in
        let Unit = f (Two ['u1] &u1) in
        u1;
        |]
      baseTest [txt|
        enum Dub (a : Lifetime)
          = Two (&a Unit) (&a Unit)
          | None;

        test : Unit
        = let u1 = Unit in
        let d = Two ['u1] &u1 &u1 in
        let Unit = (
          case d of
          | Two r1 r2 ->
            drop r1 in drop r2 in Unit
          | None -> Unit)
        in u1;
        |]

    it "can account for multiple arguments referencing the same variable" do
      baseTest [txt|
        struct Holder (a : Lifetime) { &a Unit }

        test : Unit
        = let u1 = Unit in
        let f = \(r:&'u1 Unit) (h:Holder 'u1) ->
          drop r in let Holder r = h in
          drop r in Unit
        in
        let Unit = f &u1 (Holder ['u1] &u1) in
        u1;
        |]

    it "can move a structure containing a lifetime into a closure" do
      baseTest [txt|
        struct Holder (a : Lifetime) { &a Unit }
        test : Unit
        = let u1 = Unit in
        let h = Holder ['u1] &u1 in
        let other = (\u -> let hr = &h in
          \y ->
            let Unit = u in
            let Holder ur = hr in
            drop ur in y)
          : forall M ['h] t : Type.
            Unit -M['h]> t -S['h]> t in
        let Int = other [Int] Unit Int in
        let Holder ur = h in
        drop ur in
        u1;
        |]

    it "does not always synthesize Univ as Many" do
      baseFailTest (RemovedTermVar (Var "other") es es) [txt|
        struct Holder (a : Lifetime) { &a Unit }

        test : Unit
        = let u1 = Unit in
        let h = Holder ['u1] &u1 in
        let other = (\[t:Type] (u:Unit) -> let hm = h in
          \(y:t) ->
            let Unit = u in
            let Holder ur = hm in
            drop ur in y)
            in
        let Int = other [Int] Unit Int in
        let Str = other [Str] Unit Str in
        u1;
        |]

    it "can pass references as type arguments" do
      baseTest [txt|
        id : forall M [] t : Type. t -M[]> t
        = \v -> v;

        test : Unit
        = let u = Unit in
        let ur = id [&'u Unit] &u in
        drop ur in
        u;
        |]

    it "can take a type operator application as a type argument" do
      baseTest [txt|
        struct Holder (a:Type) { a }
        id : forall M [] t : Type. t -M[]> t
        = \v -> v;

        test : Unit
        = let u = Unit in
        let h = id [Holder Unit] (Holder [Unit] u) in
        let Holder u = h in
        u;
        |]

    it "can check constructing and destructuring a generic struct" do
      baseTest [txt|
        test : Unit
        = let tup = Tuple [Str] [Int] Str Int in
        let Tuple s i = &tup in
        drop s in drop i in
        let Tuple s i = tup in
        let Str = s in let Int = i in
        Unit;
        |]

    it "can check nesting a generic struct" do
      baseTest [txt|
        test : Unit
        = let tup = Tuple [Int] [Tuple Str Str] Int (Tuple [Str] [Str] Str Str) in
        let Tuple i stup = tup in
        let Int = i in let Tuple s1 s2 = stup in
        let Str = s1 in let Str = s2 in
        Unit;
        |]

    it "can check borrowing a generic struct" do
      baseTest [txt|
        test : Unit
        = let tup = Tuple [Int] [Tuple Str Str] Int (Tuple [Str] [Str] Str Str) in
        let Tuple ir stupr = &tup in
        drop ir in drop stupr in
        let Tuple i stup = tup in
        let Int = i in let Tuple s1 s2 = stup in
        let Str = s1 in let Str = s2 in
        Unit;
        |]

    it "can check complex usage of several generic structs" do
      baseTest [txt|
        test : Unit
        = let tup = Tuple [Str] [Int] Str Int in
        let Tuple s i = &tup in
        drop s in drop i in
        let tup2 = Tuple [Int] [Tuple Str Str] Int (Tuple [Str] [Str] Str Str) in
        let Tuple s i = tup in
        let Str = s in let Int = i in
        let Tuple i stup = &tup2 : &'tup2 (Tuple Int (Tuple Str Str)) in
        let Int = copyInt ['tup2] i in
        let Tuple s1 s2 = (copy stup : &'tup2 (Tuple Str Str)) in
        drop stup in
        let Str = copyStr ['tup2] s1 in
        let Str = copyStr ['tup2] s2 in
        let Tuple i stup = tup2 in
        let Int = i in let Tuple s1 s2 = stup in
        let Str = s1 in let Str = s2 in
        Unit;
        |]

    it "makes sure copy correctly maintains the type of a sub-reference" do
      baseTest [txt|
        test : Unit
        = let tup = Tuple [Int] [Tuple Str Str] Int (Tuple [Str] [Str] Str Str) in
        let Tuple i stup = &tup : &'tup (Tuple Int (Tuple Str Str)) in
        let Int = copyInt ['tup] copy i in
        let Tuple s1 s2 = (copy stup : &'tup (Tuple Str Str)) in
        drop stup in
        let Str = copyStr ['tup] copy s1 in
        let Str = copyStr ['tup] copy s2 in
        drop s1 in drop s2 in drop i in
        let Tuple i stup = tup in
        let Int = i in let Tuple s1 s2 = stup in
        let Str = s1 in let Str = s2 in
        Unit;
        |]


    it "can take a higher kind as a type argument" do
      baseTest [txt|
        struct Hold (a:Type) { a }
        higher : forall M [] h : Type -> Type. (Unit -M[]> h Unit) -S[]> h Unit
        = \ c -> c Unit;

        test : Hold Unit
        = higher [Hold] (Hold [Unit]);
        |]


    it "can check complex usage of a generic enum" do
      baseTest [txt|
        consEnum : Either Str (Either Int Str) -M[]> Unit
        = \e1 -> case e1 of
        | InL s -> let Str = s in Unit
        | InR e2 -> case e2 of
          | InL i -> consInt i
          | InR s -> consStr s;

        test : Unit
        = let e1 = InL [Int] [Str] Int in
        let e2 = InR [Str] [Either Int Str] (InL [Int] [Str] Int) in
        let Unit = case &e1 of
          | InL i -> consInt (copyInt ['e1] i)
          | InR s1 -> let Str = copyStr ['e1] (copy s1) in drop s1 in Unit
        in case e1 of
        | InR s -> let Str = s in
          let Str = case &e2 of
            | InL s2 -> copyStr ['e2] s2
            | InR e3r -> case e3r of
              | InR s3 -> copyStr ['e2] s3
              | InL i -> let Int = copyInt ['e2] i in Str
          in consEnum e2
        | InL i -> let Unit = consEnum e2 in consInt i;
        |]

    it "can catch a borrow error in complex usage of a generic enum" do
      baseFailTest (CannotUseBorrowedVar (Var "e1") [Var "s1"] es) [txt|
        consEnum2 : Either Str (Either Int Str) -M[]> Unit
        = \e1 -> case e1 of
        | InL s -> let Str = s in Unit
        | InR e2 -> case e2 of
          | InL i -> consInt i
          | InR s -> consStr s;

        consEnum1 : Either Int Str -M[]> Unit
        = \e1 -> case e1 of
        | InL i -> consInt i
        | InR s -> consStr s;

        test : Unit
        = let e1 = InL [Int] [Str] Int in
        let e2 = InR [Str] [Either Int Str] (InL [Int] [Str] Int) in
        case &e1 of
        | InL i -> let Unit = consEnum2 e2 in
          let Int = (copyInt ['e1] i) in
          consEnum1 e1
        | InR s1 -> let Str = copyStr ['e1] (copy s1) in
        case e1 of
        | InR s -> let Str = s in
          let Str = case &e2 of
            | InL s2 -> copyStr ['e2] s2
            | InR e3r -> case e3r of
              | InR s3 -> copyStr ['e2] s3
              | InL i -> let Int = copyInt ['e2] i in Str
          in consEnum2 e2
        | InL i -> let Unit = consEnum2 e2 in consInt i;
        |]

    it "can catch taking a reference to something without kind Type" do
      baseFailTest (ExpectedKind TyKind (TyOpKind TyKind TyKind) es) [txt|
        struct Hold (a:Type) { a }
        test : forall M [] l : Lifetime.
          (&l Hold) -M[]> (&l Hold)
        = \v -> v;
        |]

    it "can catch bad type application" do
      baseFailTest (IsNotTyOp TyKind es) [txt|
        test : forall M [] l : Lifetime.
          (&l Int) Int -M[]> (&l Int) Int
        = \v -> v;
        |]

    it "can catch non-sense types" do
      baseFailTest (ExpectedKind TyKind LtKind es) [txt|
        id :
          forall M [] t : Type.
          t -M[]> t
        = \v -> v;

        test : Unit
        = let a = Str in
        let Str = id ['a] a in Unit;
        |]

    it "can catch a malformed type in return position" do
      baseFailTest (ExpectedKind TyKind (TyOpKind TyKind TyKind) es) [txt|
        struct Hold (a:Type) { a }
        test : forall M [] l : Lifetime. Unit -M[]> (&l Hold) Unit
        = \v -> v;
        |]

    it "can catch using a type instead of a lifetime" do
      baseFailTest (ExpectedKind LtKind TyKind es) [txt|
        test : Unit -M[Int]> Unit
        = \v -> v;
        |]

    it "can take a type operator as a kind argument" do
      -- TODO: I think the error is coming from the partial application???
      baseTest [txt|
        enum ListF (a:Type) (b:Type)
          = NilF
          | ConsF a b;

        struct Fix (f:Type -> Type) { (f (Fix f)) }

        test : Fix (ListF Int) = Fix [ListF Int]
          (ConsF [Int] [Fix (ListF Int)] Int
            (Fix [ListF Int]
              (NilF [Int] [Fix (ListF Int)])));
        |]

    it "can catch mismatched contexts" do
      let diffs = [[(Var "i", 0, tyCon "Int")], []]
          diffs' = (es,) <$> diffs
      baseFailTest (CannotJoinCtxs diffs' es) [txt|
        test : Unit
        = let Unit = case Left Int of
        | Left i -> Unit
        | Right s -> let Str = s in Unit
        in Unit;
        |]

    it "can catch a rank 2 type" do
      let univTy = univ Many staticLt "x" TyKind fTy
          x = tyVar0 "x"
          fTy = funTy Many x staticLt x

      baseFailTest (NoRank2 univTy) [txt|
        test : forall M [] l : Lifetime.
          &l (forall M [] x : Type. x -M[]> x) -M[]> Unit
        = \r -> drop r in Unit;
        |]

    it "can check integer literals" do
      baseTest [txt|
        i1 : I64 = 14566;
        i2 : I64 = -13561;
        |]

    it "can check string literals" do
      baseTest [txt|
        s1 : String = "hello ";
        s2 : String = "Everyone";
        |]

    it "can check multiple argument multi-use functions" do
      baseTest [txt|
        multi : forall M [] l : Lifetime.
          &l Unit -M[]> Unit -M[l]> Unit
        = \r ->
        let f = \(x:Unit) -> let rc =
          copy r in drop rc in x
        in drop r in f;
        |]

    it "correctly scopes information about when variables were dropped" do
      -- We're checking to make sure it throws UnknownTermVar rather than
      -- RemovedTermVar. This means that information about when a variable
      -- is dropped (in `varLocs`) does not persist past when it is relevant.
      baseFailTest (UnknownTermVar (Var "r3") es) [txt|
        struct Holder (a : Lifetime) { (&a Unit) (&a Unit) Unit }

        test : Unit
        = let u1 = Unit in
        let f = \[l:Lifetime](h:&l (Holder 'u1)) ->
          let Holder r1 r2 r3 = h in
          let r2c = (r2 : &'u1 Unit) in
          let r3c = r3 : &l Unit in
          drop r1 in drop r2c in drop r3c in
          Unit
        in
        let h = Holder ['u1] &u1 &u1 Unit in
        let Unit = f ['h] &h in
        let Holder r1 r2 u3 = h in
        drop r1 in drop r2 in drop r3 in
        let Unit = u3 in u1;
        |]

    it "throws an error for shadowed variables" do
      baseFailTest (VarAlreadyInScope (Var "u") es es) [txt|
        test : Unit
        = let u = Unit in
        let f = \(v:Unit) ->
          let u = Unit in
          let Unit = v in u
        in f u;
        |]
      baseFailTest (VarAlreadyInScope (Var "u") es es) [txt|
        test : Unit
        = let u = Unit in
        let f = \(u:Unit) -> u in
        f u;
        |]
      baseFailTest (VarAlreadyInScope (Var "u") es es) [txt|
        test : Unit
        = let u = Unit in
        let u = Unit in
        let Unit = u in u;
        |]
