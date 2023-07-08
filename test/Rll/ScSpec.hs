{-# LANGUAGE QuasiQuotes #-}
module Rll.ScSpec where

import Rll.ScSpecUtil

import Test.Hspec

spec :: Spec
spec = do
    (willSpec, commitUpdates) <- runIO $ prepare $ Nothing
    afterAll_ commitUpdates $ describe "specialization" do
      it "can do the bare main function" do
        willSpec Test "bare main"
          [txt|
          struct Unit {}

          main : Unit
          = Unit;
          |]
      it "can specialize an id function" do
        willSpec Test "spec id"
          [txt|
          struct Unit {}

          id : forall M [] t : Type. t -M[]> t
          = \x -> x;

          main : Unit
          = id [Unit] Unit;
          |]
      it "can specialize a simple type" do
        willSpec Test "spec simple type"
          [txt|
          struct Unit {}
          struct Holder (a: Type) { Unit }

          id : forall M [] t : Type. t -M[]> t
          = \x -> x;

          main : Unit
          = let Holder u = id [Holder Unit] (Holder [Unit] Unit)
          in u;
          |]
      it "collapses applications across parentheses" do
        willSpec Test "collapse app parens"
          [txt|
          struct Pair (a: Type) (b:Type) { a b }

          id : forall M [] t : Type. t -M[]> t
          = \x -> x;

          main : Pair I64 String
          = id [Pair I64 String] ((Pair [I64] [String] 54) "test");
          |]
      it "can specialize a function with multiple arguments and type parameters" pending
      it "can specialize a type with multiple type arguments" pending
      it "can specialize a poly lambda" do
        willSpec Test "poly lambda"
          [txt|
          struct Unit {}
          struct Holder (a: Type) { Unit }

          main : Unit
          =
          let id = \[t:Type] (x:t) -> x in
          let Holder u = id [Holder Unit] (Holder [Unit] Unit)
          in u;
          |]
      it "can specialize a partially applied constructor" do
        willSpec Test "partial con"
          [txt|
          struct A {}
          struct B {}
          struct Pair (a: Type) { a B }
          enum Some = None | Two B B;

          main : B
          =
          let id = \[t:Type] (x:t) -> x in
          let f = Pair [A] A in
          let Pair a b = f B in
          let A = a in let B = b in
          let g = Two B in
          let bout =
            case id [Some] (g B) of
            | None -> B
            | Two b1 b2 -> let B = b1 in b2
          in bout;
          |]
      it "can specialize a poly lambda that captures references" pending
      it "can specialize a poly lambda that captures moves" pending
