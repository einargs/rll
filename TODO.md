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
  - [ ] Test how fully specialized types that take higher kinded arguments are working.
- [ ] Write some tests to figure out how we should be tracking borrow counts for type variables.
  Because I have a sudden realization that I could write some bad code by using type variables.
  - Maybe? I mean, while a type variable lifetime exists we know it isn't deallocated, so isn't
    anything fine? And anything persisting has to be accounted for?
  - I'll have to actually reason this out.
- [ ] Add tests for closure environments in `Core`.
- [ ] Double check that the order of members in struct decls isn't getting reversed.
  (I think it is. Maybe it's just a glitch in pretty printing.)

## LLVM
- [ ] I think I have a bug where if you have a reference to a function and apply
  a type application to it, you get a function value instead of a reference. This
  means you could drop it again, causing a double free.
- [ ] Potential problem: how are zero argument functions/rebuilt values going to work?
  I'll have to write tests for them.
- [ ] Check whether recursive function closures become part of a closure environment
  so they can get passed on.
  - Aha -- they don't need to be; they'll just take the normal function value that the
    recursive function variable holds. We should only need the special context variable
    for recursive functions.
- [ ] Create normal variables holding the function value when we have a recursive function
  declared.
- [X] Work on breaking `genEntryFun` up so that the entry block generation isn't so monolithic.
  - [ ] Consider writing utilities to load and store to `indexStructPtr`; it would simplify
    some of the helpers in that block.
- [ ] Look into whether I can just leave `load` and `alloca` instructions with the `align` arg
  as `1` or if I need to pass the data layout around and read from that. I think that it'll
  automatically promote the alignment based on the stack alignment.
- [ ] Write a nice helper for building manual functions. Defining all the entry function args
  separate in `genFun` is annoying.
- [ ] Eventually I should list the tags for different enums constructors as part of the data type.
- [ ] I need to deal with functions that don't take any arguments for generating entry blocks.
- [ ] Change it so that instead of raw types we use more named types in the generated llvm and
  just do a little extra to calculate size of enums.
  - So like cutting out `genType` in `toLlvmType` so that I don't have the difference between
    `toLlvmType` and `toOpaqueType` getting in the way.
  - Probably need to make sure that I generate all types first. Maybe have a pass where I calculate
    type sizes for enums and store that instead of doing it dynamically. So I could break this phase
    into two parts: type gen and code gen.
- [ ] Make references to functions just raw function values.
- [ ] Some `closureArg_0` blocks in `main%.entry` in `"takes a reference to a function as an argument"`
  have no instructions in them. Not sure if this is a problem.
- [ ] I'm pretty sure that functions or function references in closure environments is going to cause
  problems when determining whether they're on the stack or not via `Moved` and `Refd`.

Next
- [X] Make integer literals copyable and dropable.
- [X] Make `genIR` generate code for literal `Int64`s.
- [ ] Add a way to have built-in functions implemented in LLVM.
  - [X] Inline builtin ops in GenLLVM.
  - [X] Generate the baseline wrappers around built-in operations.
  - [ ] I don't know if I need to generate empty `ClosureEnv` arguments for the built-in fast functions
    or not. I'm going to guess that I don't and hope the entry function still works?
  - [ ] Generate entry function wrappers around built-in operation wrappers. I'll need to somehow abstract
    this part to avoid duplication with existing entry function generation.
  - [ ] I could maybe do something to avoid duplicating code for the wrappers and built-in operations.
- [ ] Take out all the trace statements.
- [ ] I should have called them primitive functions instead of built-in functions. Consider renaming.

Future
- [ ] Remove all of the Aeson FromJSON and ToJSON stuff.
- [ ] In the future, we'll add another map to `Ctx` during type checking that will hold all `extern`
  references to C functions.
  - Maybe I should make `Tc` emit declarations? Where do I check that data types don't have
    recursive references right now.
- [ ] I need to fix that problem where either we never infer that multi-argument functions can return many
  use functions, or that the type checker rejects them even if they're explicitly defined.
  - may need to check that created functions work right
- [ ] I need to write up a list (on paper) of all the different pieces of my modules so I can separate them out.
  - Maybe use a types folder where I declare types?
- [ ] Clean up `TODO.md`; it's fine to just delete sections since they're still in git.
  - [ ] Also make like a documentation file where I can move/rewrite some documentation stuff.
- [ ] I should split `GenLLVM` into something focused on generating code for expressions, something focused
  on generating code for types, and something focused on generating functions.
- [ ] Query based compiler might be a good way to architect this when I re-organize things.

### Built-In Function Approaches
- I can add a separate SpecIR term, or I can just have the proper function definitions generated normally.
  I think I'll have the builtin function definitions generated on their own and just rely on llvm to simplify.
- I could make built-in functions normal functions that get an entry function generated for them.
  - In the future when I want external C functions, I could have an `extern` statement that causes
    it to be recorded in a separate list to be processed by the `Gen` stage?
- I could have them be a separate kind of function that must be fully invoked. This could be:
  - A type-level difference
  - Just an additional check, probably in a lower level check. I'm not a fan of that.

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

- [ ] Test that runs spec on everything and makes sure there's at least one specialized version
  for all core declarations? No, that would need a `main` function. Something like it.
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
- [ ] I think I want to maybe mark the functions that wrap constructors as always inline,
  so that the entry function inlines them.
- [ ] It feels like I'll eventually want a lower level type system/set of annotations that only
  has info relevant for llvm compilation. So like, no lifetimes, etc. Maybe turn references to
  functions into just standard function values since no need to know about that.
  - What about a way to mark variables as either pointers to the stack or raw variables? Would
    have caught some bugs. Build it into the variable generation and use?
- [ ] Figure out some kind of logging system.
- [ ] Move the mangling stuff to a new data structure instead of a bizarre shitty text thing.
- [ ] Make the entry functions for built-in functions just do the operation themselves.
  - I can make `genEntryFun` take an argument that's like `genOp` and have that either generate
    a call to the fast function or do the actual operation.
- [ ] Does `genFun` actually need to check if the function has already been generated?

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
- [ ] Could make gen and spec errors and such include a stack, since they're supposed to be
  compiler errors.
- [ ] I'm going to eventually need a function that can take a reference to an integer and give
  you an owned copy of it. This is because otherwise there's no way to get at an integer field
  of a structure without deconstructing and reconstructing the structure.
  - This kind of thing is going to need syntactic sugar. Dot access syntax if it's "copyable"?
- [ ] Currently copy can't copy a global variable. So the below fails. I probably want to keep this?
  It'll depend on how I do global variables. But if I keep it I need a better error message than
  just saying the variable doesn't exist because it doesn't look at global variables.
  ```
  i : I64 = 123;
  main : I64
  = copy i;
  ```

# Notes
- I can mimic cut in stuff by just using try on say the first part of a parser.
  See the funDecl parser.
- I finally worked out the difference between system f and f omega -- applying types at the type level.
- I'm going to just say that we should never have a subzero borrow count. Optimizations like
  that kind of "eventual consistency" open up way too many headaches.
- My type substitution code is horrifically inefficient. If there's a slowdown, look over there.
  - Especially note the way that when I do it on `Core` it means that there's no more sharing of `Ty` objects
    in `Core` stuff.

# Papers
- Paper about calling conventions in lazy languages and an IR for it.
  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/tacc-hs09.pdf
