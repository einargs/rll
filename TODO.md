# Current
- [ ] I need to implement an anti-rank-2 check.

# Compilation
I'm thinking that I'll have a fully annotated IR that stuff gets translated to as we type check.

So closures will have a list of what they need to be able to hold -- both references and moved/consumed
values.

- [ ] I need to change how I handle Univ and Poly.
- [ ] Allow rank 2 types when they're the same representation (i.e. variables inside boxes).

# Eventual Polish
These are eventual things to do for polishing.
- [X] Label all the parser nodes for better error messages.
- [ ] Avoid calculating difference between entrance and exit scopes twice for mult and consumed
  variables.
- [X] I may want to rewrite the whole LtSet stuff to keep the spans of the types around.
- [ ] Add test code to specifically check that the correct errors are triggered at the right spots.
- [ ] Remove excess `try` in the parser. Probably take it out of branch and then manually
  add try where necessary.
- [ ] Make sure variable names and such are strict text.
- [ ] Adjust the parser so that lowerText and upperText parse any kind of text, they just throw
  a parse error for incorrect capitalization.
- [X] I'm going to need like a `SpanVar` type for e.g. function arguments where I want to be able
  to point at it.
- [ ] Maybe a way of indicating a span is not directly linked to source, but inferred from that source.
- [ ] Probably create a dedicated type equality thing that ignores TyVarBinding etc so that equality
  means equality.
  - How will I handle testing then?
- [ ] A map holding info about where variables are dropped so I can give nice error messages about stuff
  being dropped.
- [ ] Rewrite some of my error messages to assume the specified type is correct not the term.
- [ ] check to make sure no top-level functions are single use. We can have top level values tho.
- [ ] Allow me to ommit the empty lifetime brackets in functions.
- [ ] How exactly does lexeme decide whether it needs to consume space at the end or not?
- [ ] Parser tests for annotation precedence -- make sure `\b -> b:T` is `\b -> (b:T)`
- [ ] Decide whether having the struct name in the data type is redundant
- [ ] Rewrite to use recursion schemes.
- [ ] See if I can optimize type substitution by only shifting once I'm replacing with the
  argument.
- [ ] Test to make sure that a TypeIsNotStruct error on a reference to a type doesn't highlight
  the entire type, just the inside of the reference type.
- [ ] Adapt the really nice highlight diffing from HSpec for when I'm saying "expected x but got y"
- [ ] Changing the closure end thing from an arrow to a dot will help avoid it being confused for a type
  and allow for better error messages.
- [ ] Eventually every error should have a test to make sure it triggers correctly.

## Better Errors
- [ ] Improve the context join error to highlight the areas that conflict and label them directly
  with the conflicting variables.

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
- I finally worked out the difference between system f and f omega -- applying types at the type level.
