# The Ray Programming Language

A WebAssembly-focused programming language for general purpose use

## Goals
- Simple, yet flexible, syntax
- A strong, inference-based type system
- Write once, run anywhere by targeting WebAssembly (specifically using WASI)

## Tooling

### Language Server

An experimental Language Server Protocol (LSP) implementation now lives in this
repository. You can launch it directly via:

```bash
cargo run -p ray-lsp
```

It currently responds to `initialize`/`shutdown` requests and is the starting
point for richer IDE integrations built atop the `ray analyze` diagnostics and
symbol metadata.

#### VS Code client

A minimal VS Code extension is under `editors/vscode`. To experiment locally:

```bash
cd editors/vscode
npm install
npm run compile
```

Then open the repository root in VS Code and use the “Run Ray LSP client” launch
configuration (defined in `editors/vscode/.vscode/launch.json`). The extension
will spawn `cargo run --quiet -p ray-lsp` and activate whenever a `.ray` file is
opened.
