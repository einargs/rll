NEXT STEP: write tests for checking functions.

- [ ] Add a way to get the names of variables from the context.
- [ ] Change case statements to infer whether they're working on a reference or not.
- [ ] What do I do about comparing variables in types when they're referred to? There are
  free variable grabbing problems with that. Maybe I need a pass that goes through and assigns
  every variable a unique identifier. That would also let me skip having to do de-brujin indices.
  - It could literally just be a monad with a map of names to ids and an incrementing id count.
- [ ] Write a pass that goes through and assigns de-brujin indices.
- [ ] How exactly does lexeme decide whether it needs to consume space at the end or not?
- [ ] Implement polymorphic types for the new data types.

# Eventual Polish
These are eventual things to do for polishing.
- [ ] Label all the parser nodes for better error messages.
- [ ] Add test code to specifically check that the correct errors are triggered at the right spots.
- [ ] Remove excess `try` in the parser. Probably take it out of branch and then manually
  add try where necessary.
