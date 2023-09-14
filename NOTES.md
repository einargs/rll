# LLVM Generation
- I don't want to use the llvm varargs stuff because then I can't get tailcall optimizations.

## LLVM Gen Debugging Tips
- when debugging an error with the IR, try emitting it and running llc on it. llc
  has much better errors.
- running `lli` (interpreter for llvm ir) with the library on the llvmir is very
  useful. You do need a `main` function.
  `lli --load=$(gcc --print-file-name=libc.so.6) ./llvmir`
