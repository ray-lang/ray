# Ray Standard Library

Ray ships with a layered library stack that balances low-level control with batteries-included conveniences. Everything lives under the workspace `lib/` directory and is bundled by the compiler into `.raylib` archives during builds (`src/libgen`).

## Layout Overview
- `lib/core`: minimal runtime surface that is injected by default; it provides strings, math helpers, iterators, and WASI shims. See `lib/core/core.ray` and sibling files.
- `lib/std`: optional, higher-level helpers built on top of core—collections, richer IO, data/time, hashing, and platform abstractions.
- `lib/libc`: precompiled WebAssembly object code and signatures for interoperating with the WASI C environment (`lib/libc/wasi_malloc.wasm` is linked automatically by the LLVM backend).

When you run `ray build`, the driver resolves imports inside this hierarchy using `ModuleBuilder` (`src/sema/modules.rs`) and links the requested libraries into the final artifact.

## Core Modules
- **`core::string`** (`lib/core/string.ray`): fundamental UTF-8 string type with concatenation, allocation helpers, and a `ToStr` implementation so strings participate in formatting.
- **`core::io`** (`lib/core/io/io.ray` and `lib/core/io/wasi.ray`): thin printing primitives (`io::print`) that call into WASI's `fd_write`.
- **`core::math`**, **`core::int`**, **`core::range`**, **`core::iter`**: numeric helpers, range iteration, and iterator traits used across the language.
- **`core::decorators`**: compiler-facing annotations such as `@inline`.
- **Memory helpers**: pointer utilities (`ptr_add`, `ptr_sub`) and allocation wrappers (`new`) live alongside the `extern` declarations in `core.ray`.

These modules avoid dependencies on the richer `std` facilities, making them safe to include for freestanding or embedded builds.

## Standard Modules
- **Collections**: `std::array`, `std::dict`, and `std::tuple` add higher-level containers and iteration helpers. Many implement the `Iterable` and `Iterator` protocols from `lib/std/mod.ray`.
- **Strings and text**: `std::string` extends the core string with slicing, UTF-8 decoding (`for b in ch_bytes` style loops), and formatting helpers.
- **IO**: `std::io` wraps libc-style `FILE` handles, offering `File::open` and `File::write` for buffered output.
- **Math and time**: packages in `lib/std/math/` and `lib/std/datetime/` expose numeric utilities and time abstractions intended for WASI environments.
- **Platform support**: `lib/std/platform` contains WASM-specific helpers, and `lib/std/sys` aggregates system-level entry points.
- **Utilities**: hashing (`lib/std/hash.ray`), printing (`lib/std/print.ray`), and protocol definitions (`lib/std/mod.ray`) provide traits and adapters adopted by user code.

Each of these modules is an ordinary Ray file; you can inspect and extend them just like project sources.

## Working Without `std`
- Pass `--no-core` (see `BuildOptions::no_core` in `src/driver/build.rs`) to disable the automatic injection of the core library. This is useful when bootstrapping the compiler or assembling minimal runtimes.
- The `examples/no_std.ray` and `examples/poly_no_core.ray` programs show how to rely solely on explicit `extern` functions and your own allocator.
- Without the prelude you must import any needed traits manually (for example, `import super::ToStr` before calling `io::print`).

## WASI And External Bindings
- Low-level WASI calls are defined in `lib/core/io/wasi.ray` and linked directly into your binary; they are thin wrappers around the WASI ABI.
- Additional libc helpers (e.g. `fopen` in `lib/std/io/io.ray`) come from the `lib/libc` bindings and the `crates/wasi_malloc` runtime shim.
- The compiler automatically adds the WASI allocator archive when generating Wasm (`src/codegen/llvm/mod.rs`), so you rarely need to manage these objects manually.
