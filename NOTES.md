# LLVM Generation
- I don't want to use the llvm varargs stuff because then I can't get tailcall optimizations.
  - [ ] I actually probably could use the var arg intrinsics and only use a c calling convention for entry
    functions. All tail call optimizations will be happening with fast functions, so that isn't even a downside.

## LLVM Gen Debugging Tips
- when debugging an error with the IR, try emitting it and running llc on it. llc
  has much better errors.
- running `lli` (interpreter for llvm ir) with the library on the llvmir is very
  useful. You do need a `main` function.
  `lli --load=$(gcc --print-file-name=libc.so.6) ./llvmir`
- Useful trick for debugging values:
  ```
  %conTag = zext i8 %constructorTag_0 to i64
  call void (ptr, ...) @printf(ptr @print_answer, i64 %conTag)
  ```
