# Ray Language Overview

Ray is a statically typed, inference-friendly language that targets WebAssembly (WASI in particular). This document highlights the pieces you need to get oriented with the syntax and day-to-day coding style.

## Goals And Design
- **Wasm-first runtime**: everything the compiler does eventually feeds into LLVM and the WebAssembly LLD linker (`src/codegen/llvm/mod.rs`).
- **Static typing with inference**: a Hindley–Milner inspired solver powered by `typing::InferSystem` infers most types, while optional annotations keep things explicit when needed.
- **Familiar surface syntax**: Ray borrows from modern systems languages—block expressions, traits, and expression-bodied functions—while keeping syntax compact.

## Hello, World

```ray
// examples/scratch.ray
fn main() {
    io::print("hello, world")
}
```

Files default to module scope. Entry points are plain `fn main` definitions; the compiler injects the WASI `_start` wrapper automatically during LIR lowering (`src/lir/generate.rs`).

## Modules And Imports
- Modules map directly to file paths. Submodules are accessed with `::` paths such as `io::print`.
- `import` pulls names into the local scope. Qualified imports (e.g. `import super::ToStr` in `lib/core/io/io.ray`) are resolved by the semantic analyzer (`src/sema/modules.rs`).
- Libraries live under `lib/` and are packaged into `.raylib` archives that the driver can link.

## Declarations And Types
- **Functions**: declare with `fn`. A trailing block introduces statements; using `=>` creates an expression-bodied function (`lib/core/core.ray`).
- **Structs**: plain product types with named fields, constructed with literal syntax (`string { raw_ptr, len }` in `lib/core/string.ray`).
- **Traits**: defined with `trait` and parameterized over regions or types (`trait ToStr['a]` in `examples/traits_no_core.ray`). Implementations live in `impl` blocks.
- **Constants and associated items**: `impl object` blocks expose shared state, e.g. `examples/impl_consts.ray`.

## Generics, Lifetimes, And Constraints
- Type parameters and region/lifetime variables are enclosed in `[...]`. Apostrophe-prefixed names (`'a`) track borrow regions and propagate through signatures.
- `where` clauses add trait requirements to type parameters (`fn print(v: 'a) -> () where ToStr['a]` in `lib/core/io/io.ray`).
- Type inference fills in unspecified types, but annotations remain available with `: Ty` on bindings and parameters.

## Control Flow And Expressions
- Conditionals and loops are expression-oriented. `if`/`else` can be used inline (`lib/std/bool.ray`) or with block bodies.
- Loops come in `while`, `for in start..<end` ranges, and `loop` constructs (`lib/std/array.ray`, `lib/core/int.ray`).
- Blocks evaluate to the final expression; statements can omit semicolons unless you need to discard a value explicitly with `_ =`.

## Memory, Pointers, And Interop
- `new(Type)` allocates using the active runtime allocator (forwarded to `malloc` in `lib/core/core.ray`). A second argument requests an array-sized allocation (`examples/ptrs.ray`).
- Pointer casts use `as`; pointer arithmetic helpers such as `ptr_add` are provided in the core library.
- External functions attach via `extern fn`, optionally tagged with a module (`extern wasi fn fd_write` in `lib/core/io/wasi.ray`).

## Error Handling And Diagnostics
- The core library uses conventional `result`/`option`-like constructs (e.g. optional tuples in iterators).
- Compile-time diagnostics originate from the semantic and typing phases and are aggregated through `Driver::emit_errors` (`src/driver/mod.rs`).

## Toolchain Hooks
- The CLI (`src/cli/mod.rs`) exposes `ray build` for compiling source files, allowing you to toggle AST dumps, IR emission, and target selection.
- Standard library layout is described in `docs/standard-library.md`; use the `--no-core` flag when bootstrapping freestanding builds.
