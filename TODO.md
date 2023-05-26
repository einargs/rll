NEXT STEP: write tests for checking functions.

- [ ] I also have to run a check to add the lifetimes in any variables consumed
  by a closure.
- [X] Change case statements to infer whether they're working on a reference or not.
- [X] Write a pass that goes through and assigns de-brujin indices.
- [ ] How exactly does lexeme decide whether it needs to consume space at the end or not?
- [ ] Implement system F omega with type functions so I can have polymorphic data types.
  - I finally worked out the difference between system f and f omega -- applying types at the type level.
- [ ] check to make sure all top level functions are multi-use.
- [ ] Allow me to ommit the empty lifetime brackets in functions.
- [ ] Parser tests for annotation precedence -- make sure `\b -> b:T` is `\b -> (b:T)`
- [ ] I do actually need the lifetime for the recursive function? No, I can make it static
  and rely on the lts to do that for me.
  - [ ] Go through and fix any code assuming that references can't have LtJoin as their lifetimes.

# Compilation
I'm thinking that I'll have a fully annotated IR that stuff gets translated to as we type check.

So closures will have a list of what they need to be able to hold -- both references and moved/consumed
values.

- [ ] I need to change how I handle Univ and Poly. Right now the hack to deal with a recursive
  function that needs to be polymorphic is just awful. (I have to take a dummy parameter and return
  the function.)
  - I could make that kind of thing part of the recursive function definition. No, that
    doesn't work because then how would normal functions work? I can't use a fix combinator.
  - No, I could make a fix combinator that only works for mult stuff and just exposes it to the
    internals?

# Eventual Polish
These are eventual things to do for polishing.
- [X] Label all the parser nodes for better error messages.
- [ ] Avoid calculating difference between entrance and exit scopes twice for mult and consumed
  variables.
- [ ] I may want to rewrite the whole LtSet stuff to keep the spans of the types around.
- [ ] Add test code to specifically check that the correct errors are triggered at the right spots.
- [ ] Remove excess `try` in the parser. Probably take it out of branch and then manually
  add try where necessary.
- [ ] Make sure variable names and such are strict text.
- [ ] Adjust the parser so that lowerText and upperText parse any kind of text, they just throw
  a parse error for incorrect capitalization.
- [ ] I'm going to need like a `SpanVar` type for e.g. function arguments where I want to be able
  to point at it.
- [ ] Maybe a way of indicating a span is not directly linked to source, but inferred from that source.
- [ ] Probably create a dedicated type equality thing that ignores TyVarBinding etc so that equality
  means equality.
  - How will I handle testing then?
- [ ] A map holding info about where variables are dropped so I can give nice error messages about stuff
  being dropped.
- [ ] Rewrite some of my error messages to assume the specified type is correct not the term.

# Feature Thoughts
Thoughts about various future features.
- [ ] Allow type annotation on `let` expressions: ``let v : T = ... in ...`
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

# Notes
- I can mimic cut in stuff by just using try on say the first part of a parser.
  See the funDecl parser.
