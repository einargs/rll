NEXT STEP: write tests for checking functions.

- [X] Change case statements to infer whether they're working on a reference or not.
- [X] Write a pass that goes through and assigns de-brujin indices.
- [ ] How exactly does lexeme decide whether it needs to consume space at the end or not?
- [ ] Implement system F omega with type functions so I can have polymorphic data types.
  - I finally worked out the difference between system f and f omega -- applying types at the type level.
- [ ] check to make sure all top level functions are multi-use.
- [ ] Allow me to ommit the empty lifetime brackets in functions.
- [ ] Parser tests for annotation precedence -- make sure `\b -> b:T` is `\b -> (b:T)`

# Eventual Polish
These are eventual things to do for polishing.
- [ ] Label all the parser nodes for better error messages.
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

# Notes
- [ ] I can mimic cut in stuff by just using try on say the first part of a parser.
  See the funDecl parser.
