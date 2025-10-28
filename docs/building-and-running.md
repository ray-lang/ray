# Building And Running Ray Programs

This guide walks through compiling the Ray compiler itself, producing `.wasm` artifacts from Ray source files, and executing them under a WASI runtime.

## Prerequisites
- **Rust toolchain**: the compiler and supporting crates are written in Rust. Install the stable channel listed in `rust-toolchain.toml`.
- **Cargo**: packaged with Rust and used for every build (`cargo build --release` gives you an optimized compiler).
- **WASI runtime**: to run generated WebAssembly modules you will want `wasmtime`, `wasmer`, or another WASI implementation.
- **LLVM/LLD**: transitively provided by the `inkwell` and `lld` crates; no manual installation is required, but you need a system toolchain capable of linking dynamic libraries.

## Building The Compiler
1. Fetch dependencies and compile:
   ```sh
   cargo build
   ```
   The binary lands in `target/debug/ray`. Use `--release` for faster code generation at the cost of build time.
2. Optional profiling support can be enabled at runtime via `--profile` (see `src/cli/mod.rs`).
3. Unit tests currently live in Rust modules; run `cargo test` if you touch compiler internals.

## Project Layout
- **Ray sources**: top-level `.ray` files under `examples/` and your own workspaces.
- **Standard libraries**: the compiler looks for libraries relative to the `root-path` (defaults to `$HOME/.ray`), but during development it is common to point at the checked-out `lib/` directory.
- **Build artifacts**: `.raylib` archives are written to `<root>/build` (see `RayPaths::get_build_path` in `src/driver/mod.rs`), while LLVM intermediates live in `target/` alongside the Rust outputs.

## Compiling Ray Code
The CLI currently exposes a single `build` subcommand (`src/cli/mod.rs`):

```sh
target/debug/ray \
  --root-path $(pwd) \
  build examples/scratch.ray \
  --target wasm32-wasip1 \
  --output-path build/scratch.wasm
```

Key switches (defined in `src/driver/build.rs`):
- `--root-path`: tell the compiler where to find `lib/` and where to place generated `.raylib` archives. Falls back to `$RAY_PATH` or `$HOME/.ray`.
- `--target` (`-t`): choose between `wasm32`, the WASI triples (`wasm32-wasip1`, `wasm32-wasip1-threads`, `wasm32-wasip2`, or legacy `wasm32-wasi`), and aliases `wasm`/`wasi` (`src/target/mod.rs`). Defaults to `wasm32-wasip1`.
- `--stdout`: emit Wasm binaries directly to standard output; handy for piping into other tools.
- `--assembly` (`-S`): stop after producing target assembly.
- `--emit-ir`: dump LLVM IR next to the output file for inspection.
- `--skip-compile` (`-K`): run the frontend (parsing, typing, LIR) without invoking LLVM.
- `--no-core`: disable the automatic import of the core library—useful for `examples/no_std.ray`.
- `--lib`: flip the module into library mode so the driver emits a `.raylib` archive instead of an executable entry point.
- `-I <path>` / `-L <module>`: extend the C include search path or link additional precompiled Ray libraries.

The build emits structured diagnostics; semantic and type errors go through `Driver::emit_errors`, grouped by file and phase.

## Running WebAssembly Outputs
1. Build your module as shown above to produce `build/<name>.wasm`.
2. Execute with your preferred WASI runtime:
   ```sh
   wasmtime build/scratch.wasm
   ```
3. If you emitted to stdout (`--stdout`), pipe directly:
   ```sh
   target/debug/ray --root-path $(pwd) build examples/scratch.ray --stdout > scratch.wasm
   wasmtime scratch.wasm
   ```
4. Debugging tips:
   - Use `--emit-ir` and `--skip-compile` to inspect LLVM IR if codegen behaves unexpectedly.
   - Combine `--print-ast` with `RUST_LOG=ray=debug` to view the parsed module and inference progress.

## Continuous And Incremental Builds
- The `Makefile` contains shortcuts such as `make core` to rebuild the core library with the freshly compiled compiler.
- When iterating on the standard library, rerun `ray build` with `--lib` to refresh `.raylib` artifacts.
- Consider scripting a simple regression runner that compiles the programs in `examples/` to catch breaking changes before committing.
