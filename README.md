# The Ray Programming Language

A WebAssembly-focused programming language for general purpose use

## Goals
- Simple, yet flexible, syntax
- A strong, inference-based type system
- Write once, run anywhere by targeting WebAssembly (specifically using WASI)

See more [here](docs/goals.md)

## Tooling

### Installing Ray

The Ray CLI and standard library bundle live in the GitHub release artifacts. The easiest way to
bootstrap them is via the hosted install scripts:

```bash
curl -fsSL https://ray-lang.org/install.sh | bash -s nightly-2025-11-06
```

```powershell
iex "& { $(irm https://ray-lang.org/install.ps1) } nightly-2025-11-06"
```

Replace the tag (`nightly-YYYY-MM-DD`, `v0.x.y`, etc.) with the release you want. The script:

- Detects your OS/arch and downloads the matching `ray` binary and toolchain bundle.
- Installs the CLI into `${RAY_PATH:-$HOME/.ray}/bin/ray` and symlinks it to `${INSTALL_BIN:-$HOME/.local/bin}/ray`.
- Extracts `core.raylib` and other assets into `${RAY_PATH:-$HOME/.ray}`.

If `${INSTALL_BIN}` isn’t on your `PATH`, add it so `ray` is globally available.

### Contributing

If you plan to work on Ray, please read through the
[contributing guide](CONTRIBUTING.md) for information on tooling, formatting,
and testing expectations.

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
