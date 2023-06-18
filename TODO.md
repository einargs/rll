# Current
## Specialization
Write a pass to specialize function code.

Questions
- How will specializing functions for other modules work?
- Do I want to have the IR include template functions and then just list how they're
  instantiated? I think that's probably better and easier for interacting with other
  modules?

Thoughts
- I could make Core figure out when we're mentioning a polymorphic function in
  a variable and then require it to have the type applications. Combine the type apps
  with just mentioning the function.
- [X] Make sure that poly lambdas can shadow.
- [X] Providing the closure environment when specializing a recursive function is
  going to be tricky.
  - I think tracking the name of the rec fun variable and specializing when
    it's used will work. Can't be used without specializing, and the trick will help.

- [X] Generate information for what values are consumed in a closure and store it in `Core`.
  - We currently allow implicit reference capture. In other words, if we define a value
    outside of a closure and create a reference to it inside the closure, that still works.
    ```
    test : Unit
    = let u = Unit in
    let f = \ x: Unit ->
      let r = &u in
      drop r in
      x in
    let Unit = f Unit in
    u;
    ```
    It will be easier to record what external variables have references taken of them
    and record that in the closure environment. Then in `Spec` we'll transform any references
    to those variables to a specific marker. `Imp` will probably keep the same form since it
    doesn't reify the closure environment.
- [X] Write name mangler.
- [X] Just go ahead and fully specialize the types now. `Imp` can use the same data
  structures probably, and this is the specialization stage.
- [ ] When synthesizing function types I need to make sure that I don't automatically make
  all Univ `Many`, because then a single-use context can be duplicated.
- [ ] Fix the broken tests for type checking after syntax changed.
  - [ ] Make the changes to the commented out test.
- [ ] Clean up commented out code in `TypeCheck.hs`.
- [ ] Add an error to `TypeCheck.hs` that requires that we have a `main` entry point
  in each module that I can start specializing from.
- [ ] Move the type substitution stuff to another file so that `Spec.hs` doesn't
  need to directly import `Tc.hs`
  - [ ] Move most of the stuff in `Tc.hs` to another file so that all the re-indexing
    stuff can just import that and be in it's own module.
- [ ] Figure out how to write tests for `Spec`. Maybe I'll write a custom parser?
  - Can just `Fix` `SpecF` too, and then write a custom comparison function.
- [ ] let's go and rewrite the parser so that all polymorphic function definition
  happens in a `let x y = ... in` or function definition. Lambdas are strictly normal.
  - This will make things easier I think?

Spec tests
- [ ] Make sure that you can't alias a polymorphic function.
- [ ] Write tests for how specializing references to functions should work.

## Imp
- The `Imp` stage will have specific "instructions" for whether a function is
  immediately invoked or is partially applied and results in a thunk.
- [ ] Make explicit the types of partially applied functions etc.
  - How do constructors play into this? I guess they have to be partially applied functions.
    Later I can optimize and do runtime trickery.
- [ ] Maybe want to start including the data type in each case and let struct
  in the `Core` stage? We'll see if this is useful for `Imp`.

## LLVM
- [ ] Install LLVM.
- [ ] Get a micro-example of a module compiling with some literal llvm code.
- [ ] Write out a compile monad for turning Elab into LLVM.
- [ ] Transform RLL structures into LLVM structures.
- [ ] Transform RLL enums into LLVM structures.
- [ ] Start compiling functions.

## Figure out
- [ ] How to do tagged unions.
  - It looks like I'll need to directly get the size of the member structs
    and then find the largest. There seems to be a `getTypeAllocSize` FFI I
    might be able to call.
  - Maybe look at how Dex does this? See Google Keep notes.
- [ ] How to call a print in llvm.

# Compilation
I'm thinking that I'll have a fully annotated IR that stuff gets translated to as we type check.

So closures will have a list of what they need to be able to hold -- both references and moved/consumed
values.

## Stages
- First we have the `Tm` stage, which I should probably go through and rename to like `SourceTm`.
- Then we have a `Core` where every term is annotated with it's type.
- Then we have a `Spec` where we specialize all the functions.
  - Eventually this will still be able to have polymorphic functions as long as
    the polymorphism is contained within references.
  - This stage will also remove all lambdas.
- Then we have `Imp` where we'll fully define what thunks and context pointers will look like.
  - Probably also will turn enums into structs and use casts. Actually, no, I'll probably have to
    wait on that because I need LLVM info about alignment and shit.
  - Top level values are treated as no-argument functions to build those values.

When we implement traits, I think that `Spec` will be where we elaborate all of the traits to stuff.
- Or that might happen with resolving traits in `Core` and then making the vtables explicit in
  `Imp`.

## Eventually
- [ ] Allow rank 2 types when they're the same representation (i.e. variables inside boxes or references).
  - I don't know how useful things like dynamic traits and rank 2 stuff will be.
- [ ] Look at existing LLVM infrastructure for converting moves and such into mutations.
  - [ ] Read through the annotations you can add to see what I can tell LLVM.
  - [ ] Run various LLVM optimization passes to see what they can do.
  - [ ] Try the passes on larger examples.

# Future Tests
Future tests.

- [ ] A bunch of tests for substitution.
  - [ ] Given `\x.\y. Pair Int x` (in univ) and we sub for `x` it works right?
  - [ ] Expand "shifts type variable indices for term variable types"
- [ ] Does the way that term functions can elide univ bindings cause any type var index
  conflicts with types generated by checking against a full list when we generate `Core`
  and (I think?) merge some of the types?
- [ ] I need a bunch of tests for multiples of stuff. I've found parse order errors,
  as well as several errors in stuff like pulling apart function and univ types giving
  the args in the wrong order.
- [ ] Tests to make sure not fully applying types to a polymorphic function is caught
  in type checking.
  - Note that there's still a thing where they can end up used as values
    because that check happens in `Spec`.
- [ ] Test to make sure type variable shadowing is working.
- [ ] Enums with 2+ values in a branch.
- [ ] Mixing no value and associated value cases in an enum.
- [ ] 3+ branches for a case statement.
- [ ] it will throw an error if a data type has a member with a kind that isn't Type
- [ ] will throw an error if we use a function out of order.
  - Eventually I want mutual recursion and pre-declaration, but this *should* be current
    behavior so nail it down.
- [ ] Write a test to make sure that applying type arguments to a reference to a poly
  function gets you a reference to the resulting function and not a value.
- [ ] Add test code to specifically check that the correct errors are triggered at the right spots.
- [ ] Write some tests to make sure I can't trigger any problems with e.g. cloning and dropping my
  static lifetime references (i.e. recursive function references).

# Eventual Polish
These are eventual things to do for polishing.
- [X] Label all the parser nodes for better error messages.
- [X] I'm going to need like a `SpanVar` type for e.g. function arguments where I want to be able
  to point at it.
- [X] Add a `BuiltinType` to `DataType` for `String` and `I64`.
- [X] I may want to rewrite the whole LtSet stuff to keep the spans of the types around.
- [X] Make sure variable names and such are strict text.
- [X] Rewrite to use recursion schemes.
- [ ] Let you write applying multiple types as a comma separated list?
  - Eh, not a big deal since I want to eventually use inference for that.
  - I do want to improve error messages for if you accidentally put a type application
    after a term application. But no need right now since things will change.
- [ ] The right side of spans are weirdly broken, often being way bigger than the line.
- [ ] Context that keeps track of the names of type variables for debugging to help figure out
  when indices have messed up.
- [ ] Adjust the parser so that lowerText and upperText parse any kind of text, they just throw
  a parse error for incorrect capitalization.
- [ ] check to make sure no top-level functions are single use. We can have top level values tho.
- [ ] Rewrite to use the full recursion scheme library.
- [ ] Avoid calculating difference between entrance and exit scopes twice for mult and consumed
  variables.
- [ ] Remove excess `try` in the parser. Probably take it out of branch and then manually
  add try where necessary.
- [ ] Maybe a way of indicating a span is not directly linked to source, but inferred from that source.
- [ ] Probably create a dedicated type equality thing that ignores TyVarBinding etc so that equality
  means equality.
  - How will I handle testing then?
- [X] A map holding info about where variables are dropped so I can give nice error messages about stuff
  being dropped.
- [ ] Rewrite some of my error messages to assume the specified type is correct not the term.
- [ ] Allow me to ommit the empty lifetime brackets in functions.
- [ ] How exactly does lexeme decide whether it needs to consume space at the end or not?
- [ ] Parser tests for annotation precedence -- make sure `\b -> b:T` is `\b -> (b:T)`
- [ ] See if I can optimize type substitution by only shifting once I'm replacing with the
  argument.
- [ ] Test to make sure that a TypeIsNotStruct error on a reference to a type doesn't highlight
  the entire type, just the inside of the reference type.
- [ ] Adapt the really nice highlight diffing from HSpec for when I'm saying "expected x but got y"
- [ ] Add tests for parsing character escape sequences, though since that's done by megaparsec that
  might not be needed.
- [ ] I could do all of the `sanityCheckType` inside of `indexTyVarsInTm`. I think I'd have to change
  `sanityCheckType` for it.
  - I don't think I want to do this.
- [ ] Allow mutually recursive functions and using a function before it's defined.

## Better Errors
- [X] Improve the context join error to highlight the areas that conflict and label them directly
  with the conflicting variables.
- [ ] Eventually every error should have a test to make sure it triggers correctly.
- [ ] Make type arguments in lambdas bind a Span to the TyVarBinding or whatever for better error
  messages.

## Reorganize Code
- [ ] Split TypeCheckSpec into multiple files.
- [ ] Factor stuff out of `Tc.hs`.
  - [ ] Move the type variable renaming stuff into it's own file.
  - [ ] I really hate that I have to import `Core.hs` right now for the core
    substitution thing. If I type substitution and renaming to it's own file
    then `TypeCheck.hs` and `Spec.hs` can import that on their own.
  - [ ] Maybe move the `LtSet` stuff to their own file?

# Feature Thoughts
Thoughts about various future features.
- [ ] Allow type annotation on `let` expressions: ``let v : T = ... in ...`
- If I ever want to be able to specify the return type I'll need to change from an arrow to a dot.
  But I'll probably switch to defining them with `let f x y = ...`
- [ ] I could make let-struct not require you to list the struct constructor name. That would
  make it more like destructuring in other languages.
- [ ] The trick to dealing with rank-n types is to allow it only over pointers, where the runtime
  representation will be the same and we can stuff the trait into a virtual table.
- [ ] The idea of being able to slice arrays into pieces and work on those.
- [ ] How do I handle a top level bare term that isn't a function? Do I make it a zero argument
  function? I think that makes the most sense but it seems unintuitive.
- [ ] To avoid having to write S and M for functions, I could have S be a `~>` and M `->`. Then
  make the lifetime list optional if it's empty.
- [ ] Can I add an ability to "move" a multi-use function into a closure so that I can use it
  without it being borrowed, but still have the closure type check as multi-use?
- [ ] Operators.
  - Very useful module that can build an expression parser given a table of operators.
    https://hackage.haskell.org/package/parser-combinators-1.3.0/docs/Control-Monad-Combinators-Expr.html

# Notes
- I can mimic cut in stuff by just using try on say the first part of a parser.
  See the funDecl parser.
- I finally worked out the difference between system f and f omega -- applying types at the type level.
