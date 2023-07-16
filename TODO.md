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
  - [ ] Test name mangler.
- [X] Just go ahead and fully specialize the types now. `Imp` can use the same data
  structures probably, and this is the specialization stage.
  - [ ] Test how fully specialized types that take higher kinded arguments are working.
- [X] Fix the broken tests for type checking after syntax changed.
- [ ] Write some tests to figure out how we should be tracking borrow counts for type variables.
  Because I have a sudden realization that I could write some bad code by using type variables.
  - Maybe? I mean, while a type variable lifetime exists we know it isn't deallocated, so isn't
    anything fine? And anything persisting has to be accounted for?
  - I'll have to actually reason this out.
- [X] When synthesizing function types I need to make sure that I don't automatically make
  all Univ `Many`, because then a single-use context can be duplicated.
- [ ] Add tests for closure environments in `Core`.
- [X] Move the type substitution stuff to another file so that `Spec.hs` doesn't
  need to directly import `Tc.hs`
  - [X] Move most of the stuff in `Tc.hs` to another file so that all the re-indexing
    stuff can just import that and be in it's own module.
- [ ] Double check that the order of members in struct decls isn't getting reversed.
  (I think it is. Maybe it's just a glitch in pretty printing.)
- [X] BUG: Right now if a data type doesn't get mentioned in a function deriving from `main`,
  it doesn't get specialized -- even if it's in an unused case of an enum that is mentioned.

Spec tests
- [ ] I'll write the tests by having a good pretty printer and manually checking that
  it looks right, then getting a serialized output and sticking it in.
  - I'll use `Aeson` package.
- [ ] Make sure that you can't alias a polymorphic function.
- [ ] Write tests for how specializing references to functions should work.
- [X] Add a pass to the spec stuff that iterates over all of the produced types
  in the spec IR and makes sure there's no type variables.

## Imp
- The `Imp` stage will have specific "instructions" for whether a function is
  immediately invoked or is partially applied and results in a thunk.
- Mechanically I think `VarSF` and `CopySF` become the exact same thing when dealing with
  a reference: copying the pointer.
- [ ] I need to implement Box and a recursive check by this point, because otherwise
  recursive data types are infinite in size.
- [ ] Implement basic calling convention.
- [ ] Maybe want to start including the data type in each case and let struct
  in the `Core` stage? We'll see if this is useful for `Imp`.
- [ ] I'm going to need to work out tools for generating the values for enum tags
  and for accessing them and such. Maybe I'll have an `ImpDataType`
- [ ] Eventually I might want to convert types in the spec layer into a new kind
  of fully applied type with type level distinguishment between data types and
  function types. That would make some of my functions nicer.

## LLVM
- [X] I'm going to have to redo everything to use `alloca` so that taking the reference
  of something actually means a damn.
  - You can't take the reference of a reference, so I guess that could be a normal variable.
    - That might mean I have to pass around the type of stuff so I know if I need to load
      it? Well, I guess I already do need to do that.
  - Actually easier than I thought. `genIR` could still return variables holding values.
    Just needed logic to load from those variables at `VarSF` etc.
- [ ] I think I want to maybe mark the functions that wrap constructors as always inline,
  so that the entry function inlines them.
- [ ] I need some way to get information about the data type for constructors and cases.
- [X] In the future I can make it so that I don't store references on the stack?
- [X] Currently in the middle of adding the type of the dropped variable to `Drop`.
  - [X] This means I need to fix all of the type substitution code.
  - [X] Also need to fix the test code.
- [ ] I think I have a bug where if you have a reference to a function and apply
  a type application to it, you get a function value instead of a reference. This
  means you could drop it again, causing a double free.
- [ ] Before generating IR for the body of a function, we need to precalculate their
  types. Or I could use named types.
- [ ] Potential problem: how are zero argument functions/rebuilt values going to work?
  I'll have to write tests for them.
- [ ] Check whether recursive function closures become part of a closure environment
  so they can get passed on.
  - Aha -- they don't need to be; they'll just take the normal function value that the
    recursive function variable holds. We should only need the special context variable
    for recursive functions.
- [ ] Create normal variables holding the function value when we have a recursive function
  declared.
- [X] Double check that shadowing a variable creates a type error so that we don't have
  to worry about creating fresh names.
  - If I ever need to, I can disambiguate names during `Spec`.
  - Make sure that this also applies to recursive function names.
- [X] Inside the generated IR I should drop closures when they're consumed instead of relying
  on the entry function to do it if necessary.
  - I should have that working using the type of the called function value. If it's bare, I know
    I should free the closure pointer.
- [X] Work on breaking `genEntryFun` up so that the entry block generation isn't so monolithic.
  - [ ] Consider writing utilities to load and store to `indexStructPtr`; it would simplify
    some of the helpers in that block.
- [X] `genEntryFun` should be working.
- [ ] Look into whether I can just leave `load` and `alloca` instructions with the `align` arg
  as `1` or if I need to pass the data layout around and read from that. I think that it'll
  automatically promote the alignment based on the stack alignment.
- [ ] Write a nice helper for building manual functions. Defining all the entry function args
  separate in `genFun` is annoying.
- [ ] Instead of saturated and unsaturated entry functions, what I'll do is have the entry
  function take a stack allocated pointer that I'll write the return value to.
- I could write an llvm function that calls the entry function with the correct number of args
  on the stack based on a number in the closure ptr that says how many it can still accept.
  The entry function would return a raw union of a function value and the return type that this
  function would know how to interpret and cast based on info. Then it would loop over that
  part until it had called everything.
  - I think this is basically the worst parts of eval/apply and push/enter.
- [ ] Eventually I should list the tags for different enums constructors as part of the data type.

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
- [ ] Implement uncurrying.
  - In `Spec` if I find situations of `let f = ClosureCall f in ...` then I can propagate that `f` out
    to later usages of it. That will help me immediately invoke the function. (This is part of uncurrying.)
- [ ] LLVM has lifetime intrinsic stuff: https://llvm.org/docs/LangRef.html#int-lifestart
- [ ] Implement strings.
  - Actually this probably going to need string refs as well that can make a distinction between things.

## Calling Methods
### New
- Context is the struct generated by the `ClosureEnv`.
- Closure pointer is the context + partially applied arguments.
- Function value is the closure pointer and function pointer.
- When we call something, we `alloca` a struct with all of the arguments on the stack.
- If we have more arguments than we need, we find the start of the next few arguments.

- Maybe I should look into eval/apply and caching stuff.

- [ ] Problem: how do I make the return type of the slow function consistent? It needs to
  return both fun values for if the arguments are insufficient and the return type if
  they are sufficient.
  - I also have the problem of how do I know what the return type of the second function
    is in order to call it if I have extra arguments?
  - My first thought is this: when we call a function we can statically know whether we
    have enough arguments to fully saturate it to the point where it won't return a function
    type. We could use that to generate two different slow functions.
    1. One which knows that it will always return a function value, and as such knows
       that a second call will also always return a function value.
    2. And one that knows the arguments will fully saturate all arguments and thus returns
       the ultimate return type and knows that a second call, if necessary, will also
       return that type.
- [ ] Eventually look into using C vararg conventions to pass arguments to wrapper/unpack
  functions. LLVM has builtin support in the form of `va_arg` instructions among other
  things.

Placeholder Closure Pointer
- We copy and add the new arguments.
- If it's single use we drop the previous version. If it's multi-use we drop
  everything when we drop the multi-use function. Or when it's consumed.
- TODO how do we figure out whether we've been switched from multi- to single-use
  by applying arguments?
- [ ] We'll annotate every argument with `Single` or `Many`. Then we can case on
      them when we're generating the switch statement in the thing. What matters
      is whether the part of the function we will start calling is single- or
      multi-use. So if we have a partially applied function that has left
      `I64 -M[]> I64`, then our argument will be `Many`.

Eventual Closure Pointer
This is the eventual, optimized behavior we'll use.
- If we're dealing with a single use function, we allocate the rest of the arguments
  in the closure pointer and then mutate it.
  - Then once we're done with it and have pulled the arguments to apply them, we
    call a bitch.
- If we're dealing with a multi-use function we allocate only what we need and copy
  to a newly allocated pointer every time we need to.
- Within a function with arity, we know that once it becomes single use it will
  stay single use.

- I need to do push enter. I can't think of a good way to generate the apply functions.
- I'll alloca arguments on the stack and then pass the pointer to them alongside the closure
  pointer to the slow entry function.
  - The arity of the function will already be known statically, so I'll switch on the count
    in the closure pointer. That will tell me how many things to load from the closure pointer
    and how many to load from the stack.
  - I'll need to know if a function value is single use 
  - For each number of known arguments I'll generate a new 


### Old
- `ClosureEnv` will be translated to a struct when we translate to LLVM.

- Partially applied constructors will have functions wrapped around them for eta-expansion.
  - `Spec` layer.
- All function values will be a pointer to a heap allocated object with all the information
  needed for partial applications.
  - The layout of the object is:
    * the function pointer
    * arity of the function
    * number of arguments in the pointer
    * array of accumulated arguments
  - This will be a generated struct.
    - The guarentees of single-use and multi-use functions will ensure that if we have multiple
      versions memcpying them will be safe.
- All functions have an arity `n`. They can be applied to fewer or more values than `n` (if it
  returns a function). `n` is, in essence, the number of arguments to the compiled llvm function.
- Closures will accept an environment structure as the first argument.
  - This will contain all referenced and moved values.
- Calls to *known* functions can do one of two things: if there are enough arguments to fully
  saturate the known function's arity, then we just immediately invoke it. Otherwise we turn
  it into a partial application object on the heap.
- Eventually we will have two functions for each function. One that actually runs the code,
  which can be immediately invoked, and one that unpacks info from the context pointer.
  - Theoretically it will be better to have this basically be two contigous pieces of code
    that fall through instead of actually jumping. Hopefully LLVM can do that optimization
    itself.
  - For now we're just going to implement all functions as taking the context pointer and
    and unpacking args from that.
- Every time we add arguments to a non-statically known function we will check if we have
  fully saturated the arity and then load it all in.
- According to a paper, eval/apply is the superior method.
  - Eval/apply basically tracks the arity of the function in the function closure and makes
    the caller check whether there are enough arguments to call yet.
  - Paper: https://www.cs.tufts.edu/comp/150FP/archive/simon-peyton-jones/eval-apply-jfp.pdf

Implement In Spec
- [X] For partially applied constructors, generate a corresponding function that immediately
  calls the constructor that we can partially apply.

Later optimizations
- [ ] Annotate function declarations with a sequence of statically known arities of functions
  to help with generating code that immediately invokes it.
- [ ] Generate two functions for each actual function: one that actually does the code,
  which can be immediately invoked, and one that 
- [ ] When we have a statically known function, we can use the known arity to immediately
  invoke it without having to package shit up.

### Papers
- Talking about uncurrying for immediate calling of a function pointer.
  https://xavierleroy.org/publi/higher-order-uncurrying.pdf
- Defunctionalization.
  https://dl.acm.org/doi/10.1145/3591260
- Comparing eval/apply and push/enter as ways to deal with currying functions.
  https://www.cs.tufts.edu/comp/150FP/archive/simon-peyton-jones/eval-apply-jfp.pdf
  - pg 426 starts a discussion of actual implementation.

# Future Tests
Future tests.

- [ ] Write some tests for the functionality of `toRef` -- i.e. pattern matching on a reference
  to a datatype and getting the original type for members that are already references. I want to
  make sure the borrow count stuff works right.
- [ ] Write a bunch of tests to make sure that unstable borrow count errors happen properly.
- [ ] A bunch of tests for substitution.
  - [ ] Given `\x.\y. Pair Int x` (in univ) and we sub for `x` it works right?
  - [ ] Expand "shifts type variable indices for term variable types"
- [ ] Does the way that term functions can elide univ bindings cause any type var index
  conflicts with types generated by checking against a full list when we generate `Core`
  and (I think?) merge some of the types?
- [ ] I need a bunch of tests for multiples of stuff. I've found parse order errors,
  as well as several errors in stuff like pulling apart function and univ types giving
  the args in the wrong order.
- [ ] I had `ltsInTy` including the input and output of functions which could have been a problem.
  - It was only used for figuring out the lifetimes of consumed things in `ltsInConsumed`.
- [ ] More tests involving returning structs.
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
- [ ] Write tests for `addMultToArgs`.
- [ ] `willGen` isn't throwing the right error for forgetting to apply types to `extractRight`.
  ```
      willGen [txt|
        struct Unit {}
        struct L { }

        struct R { Unit Unit }

        struct Tuple (a:Type) (b:Type) { a b }

        extractRight : forall M [] l:Lifetime. forall M [] a:Type. forall M [] b:Type.
          &l (a -M[]> Unit) -M[]> Tuple L R -M[l]> R
        = \destroyLeft tup ->
        let Tuple l r = tup in
        let Unit = destroyLeft l in
        r;

        enum Two = Left L | Right R;

        main : Two
        = let tup = Tuple [L] [R] L (R Unit Unit) in
        let destroyL = \(l:L) -> let L = l in Unit in
        Right (extractRight &destroyL tup);
        |]
  ```

# Eventual Polish
These are eventual things to do for polishing.
- [ ] Improve pretty printing for multiple type applications. Right now `Pair I64 String`
  becomes `(Pair I64) String`.
- [ ] Improve pretty printing of `SpecIR`; parentheses are messed up.
- [ ] Pretty printing specialization errors?
  - [ ] A specific error for no `main` function to be an entry point.
- [ ] Would `checkStableBorrowCounts` be better if it used a `ClosureEnv`?
- [ ] Make QuoteTxt remove excess indentation. And probably discard an empty first line? No.
- [ ] Look into making `addVar` always call `incRef` on the type. Right now the problem is
  `letClause`.
- [ ] Maybe rewrite to use the full recursion schemes library.
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
- [ ] Check that all excess `try` has been removed from the parser.
  - Probably take it out of branch and remove branch.
- [ ] Maybe a way of indicating a span is not directly linked to source, but inferred from that source.
- [ ] Probably create a dedicated type equality thing that ignores TyVarBinding etc so that equality
  means equality.
  - How will I handle testing then?
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
- [ ] Move `Tm` to it's own file separate from type and such.
- [ ] Figure out how to calculate the alignment for `load` instructions so I don't have to default to `1`.
- [ ] It might be better to add the multiplicities to arguments in the `Core` IR, but doing it in
  spec works perfectly fine for now. And it avoids having to worry about the multiplicities of polymorphism.
- [ ] Once I've worked out all the ways I want to mangle things, I can use a data structure for `MVar`s
  and then when I finally convert them to text I'll use a lazy text to accumulate everything and then convert
  straight to a single strict text.

## Better Errors
- [X] Improve the context join error to highlight the areas that conflict and label them directly
  with the conflicting variables.
- [X] Label all the parser nodes for better error messages.
- [ ] Figure out a way to improve the error messages for when a function is referencing an argument
  being passed to it. Right now the error is caught because we decrement `f`'s `lts` after we
  check the argument (`u1`), but the `deleteVar` that removes `f` happens once we `synth` `f`.
  ```
  struct Holder (a : Lifetime) { &a Unit }
  test : Unit
  = let u1 = Unit in
  let f = \(u:Unit) -> let ur = &u1 in
    drop ur in u in
  let Unit = f u1 in
  Unit;
  ```
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
- [ ] Rename `ClosureEnv` to help disambiguate between a closure pointer/object,
  a function value, and the structure holding all free variables in a closure.

# Feature Thoughts
Thoughts about various future features.
- [ ] let's go and rewrite the parser so that all polymorphic function definition
  happens in a `let x y = ... in` or function definition. Lambdas are strictly normal.
  - This will make things easier I think?
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
- Eventually lookup global flow analysis stuff.
- [ ] Look at how to make a function that returns multi-use functions easy. I think this basically
  means figuring out if the arguments are copyable and then doing them that way.
  - Currently this doesn't work:
    ```
    multi : forall M [] l : Lifetime.
      &l Unit -M[]> Unit -M[l]> Unit
    = \r x -> drop r in x;
    ```
  - Instead we have to do this. Note that this works because we assume a lifetime type variable
    lasts the entire function.
    ```
    multi : forall M [] l : Lifetime.
      &l Unit -M[]> Unit -M[l]> Unit
    = \r ->
    let f = \(x:Unit) -> let rc =
      copy r in drop rc in x
    in drop r in f;
    ```
- [ ] Check if I can use types before they're declared in either other types or functions.
- [ ] Something that lets me pass a multi-use function as a single use. Subtyping?

# Notes
- I can mimic cut in stuff by just using try on say the first part of a parser.
  See the funDecl parser.
- I finally worked out the difference between system f and f omega -- applying types at the type level.
- I'm going to just say that we should never have a subzero borrow count. Optimizations like
  that kind of "eventual consistency" open up way too many headaches.
- My type substitution code is horrifically inefficient. If there's a slowdown, look over there.
  - Especially note the way that when I do it on `Core` it means that there's no more sharing of `Ty` objects
    in `Core` stuff.
