NEXT STEP: write tests for checking functions.

- [ ] Write out when I need to check if a variable is shadowed.
- [ ] Write out how a lifetime type variable being shadowed interacts with
  things.
- [ ] Write out how to check that all variables for a scope have been dropped,
  and when to check that.
  - How does shadowing work for that?
- [ ] Type equality that ignores variable names.
- [ ] Look at changing the way I do lifetimes, so that RefTy just has a single
  variable and Univ and MFunc have lists of variables. I don't think this works
  because of type variables right? I think I can just have function types have
  lists of lifetimes? No, because I need to be able to pass a list in a variable
  to a function type.
- [ ] Add a way to get the names of variables from the context.
- [ ] Change case statements to infer whether they're working on a reference or not.
