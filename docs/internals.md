# Ray Compiler Internals

This overview follows a Ray source file through the compiler, spotlighting the Rust modules that implement each phase.

## High-Level Pipeline
`Driver::build` (`src/driver/mod.rs`) orchestrates compilation:
- Resolve the module graph with `sema::ModuleBuilder`, loading `.ray` files and cached `.raylib` archives.
- Expand and normalize declarations, then run the type-inference pipeline.
- Lower the typed AST into Ray’s low-level IR (LIR) and transform it into LLVM IR.
- Invoke LLD to stitch the object code and runtime shims into a WebAssembly binary.

Diagnostics raised at any stage bubble up through `Driver::emit_errors`, which groups messages by source file and phase.

## Parsing Pipeline
- **Lexing**: `src/parse/lexer` tokenizes input using handwritten rules defined in that module. The EBNF in `docs/grammar.ebnf` exists purely for documentation; it does not feed the lexer or parser.
- **Parsing**: the Pratt-style parser lives under `src/parse/parser/`, with dedicated modules for declarations, expressions, control flow, and types. It produces `ast::Node` wrappers defined across `src/ast`.
- **AST modifiers**: `src/ast/modifier` runs post-parse adjustments such as rewriting implicit returns and attaching IDs so later passes can look up definitions efficiently.

## Semantic Analysis
- **Module resolution**: `src/sema/modules.rs` drives `ModuleBuilder`, mapping `import` paths to files, watching for circular dependencies, and loading binary `.raylib` archives.
- **Name resolution**: `src/sema/nameresolve.rs` traverses the AST, attaching fully-qualified `Path` objects and recording which trait and struct definitions a module depends on.
- **Monomorphization and mangling**: `src/sema/monomorphize.rs` specializes polymorphic definitions once inference has chosen concrete substitutions, while `src/sema/mangle.rs` turns Ray paths into linker-safe symbol names.
- **Library generation**: `src/libgen` serializes resolved modules into `.raylib` artifacts that subsequent builds can reuse without re-type-checking.

## Type System
- Constraint collection lives in `src/typing/collect`. Every expression contributes predicates and equality constraints to a tree structure (`typing::constraints`).
- `InferSystem` (`src/infer/mod.rs`) flattens those constraints and hands them to the greedy solver from the `top` crate. Trait declarations become `Class` entries, and `impl` blocks become `Instance`s.
- Solutions propagate through `TyCtx`, updating stored type schemes (`TyScheme`) and qualifying definitions with any remaining predicates.
- Errors produced by the solver are wrapped as `RayErrorKind::Type` and include precise spans via the shared `SourceMap`.

## Lowering To LIR
- LIR lives under `src/lir/` as a control-flow graph tailored for WebAssembly. Builders allocate SSA-ish temporaries, blocks, and symbol tables.
- `lir::Program::generate` (`src/lir/generate.rs`) visits AST declarations, emits LIR instructions, and synthesizes wrapper functions. `_ray_main` calls every linked library’s `main`, and `_start` provides the WASI entry point.
- Transformation passes in `src/lir/transform` clean up block structure and prepare control flow for LLVM lowering.

## LLVM Code Generation
- `codegen::llvm::codegen` (`src/codegen/llvm/mod.rs`) maps LIR constructs onto LLVM IR using Inkwell. It tracks type layouts, caches struct definitions, and ensures WASI globals exist.
- A small pass manager (promote-mem2reg, LICM, CFG simplification, etc.) runs before verification.
- The backend emits an object file, links it with `wasi_malloc.wasm`, and calls `lld::link` with the configured WASI triple (default: `wasm32-wasip1`, falling back to `wasm32-wasi` for older toolchains) to produce the `.wasm` output at the requested path.

## Runtime And Tooling Notes
- The allocator shim and other C interop helpers reside in `lib/libc` and the `crates/wasi_malloc` project; they are bundled automatically during codegen.
- CLI flags in `BuildOptions` (`src/driver/build.rs`) let you introspect intermediate representations (`--print-ast`, `--emit-ir`, `--skip-compile`), which is invaluable when debugging new passes.

## Future Directions
- Enrich the LIR with SSA form and explicit dataflow so heavier optimizations become viable.
- Broaden diagnostic coverage in `typing::error` and semantic analysis to surface more actionable messages.
- Add additional CLI entry points (`run`, `fmt`) that leverage the driver without forcing contributors to script calls manually.
