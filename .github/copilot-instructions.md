# Ray Language Compiler - AI Agent Instructions

## Project Overview
Ray is a WebAssembly-focused programming language compiler written in Rust. The compiler translates Ray source code into WebAssembly using WASI (WebAssembly System Interface).

## Key Components

### Compiler Pipeline
The compiler follows a standard pipeline architecture:
- **Parsing** (`src/parse/`): Lexer and parser for Ray source code
- **Semantic Analysis** (`src/sema/`): Name resolution and type checking
- **Type System** (`src/typing/`): Inference-based type system with constraints
- **LIR** (`src/lir/`): Low-level IR generation before LLVM
- **Codegen** (`src/codegen/llvm/`): LLVM-based WebAssembly code generation

### Standard Library Structure
- `lib/core/` - Core language features
- `lib/std/` - Standard library modules
- `lib/libc/` - C interop layer

## Development Workflow

### Building the Project
```bash
cargo build  # Debug build
cargo build --release  # Release build
```

### Project Layout Conventions
1. Core compiler modules in `src/`:
   - Each major phase has its own module (parse, sema, typing, etc.)
   - Utilities and shared code in `utils/` and `collections/`
2. Standard library code in `lib/`:
   - Core language features separated from standard library
   - Platform-specific code in `std/platform/`

### Key Patterns

#### Type System
- Uses constraint-based type inference (`src/typing/infer/`)
- Type schemes defined in `src/typing/ty.rs`
- Example type annotation: `fn example(x: int) -> string`

#### Module System
- Modules map to directories by default
- Entry points defined in `mod.ray`
- Cross-module dependencies handled in `src/sema/modules.rs`

## Common Tasks

### Adding a New Language Feature
1. Add grammar rules in `docs/grammar.ebnf`
2. Implement parsing in `src/parse/parser/`
3. Add semantic analysis in `src/sema/`
4. Update type system constraints in `src/typing/` if needed
5. Add codegen support in `src/codegen/llvm/`

### Testing
- Add example programs in `examples/`
- Run tests with `cargo test`
- Test standard library features in `lib/std/`

## Integration Points
- LLVM integration via inkwell crate
- WASI target configuration in `src/target/`
- C interop through `lib/libc/`
