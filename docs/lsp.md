# Ray Language Server (ray-lsp)

This document describes the current state of the Ray language server, highlights
the features that already work, and notes the next steps to keep in mind as we
iterate. Treat it as a living document – update it whenever behaviour changes or
new capabilities land.

## Architecture Overview

ray-lsp is a standalone binary crate that uses `tower-lsp` (0.20.x) to talk to
editors that speak the Language Server Protocol. The binary runs inside the
workspace (see `crates/ray-lsp/src`) and depends directly on the Ray compiler
crate, exposing compiler functionality to editors.

Key modules:

| Path | Responsibility |
|------|----------------|
| `src/main.rs` | LSP server entry point, request handlers, in-memory document store |
| `src/semantic_tokens.rs` | Bridges the compiler lexer to LSP semantic tokens |

The server currently keeps the full text of every open document in a simple
`RwLock<HashMap<Url, String>>`. There is no persistent state across sessions.

## Supported Features

### Initialization
- Responds to `initialize` with basic server info.
- Advertises semantic token support (`textDocument/semanticTokens/full`) with a
  static legend that includes keywords, variables, numeric literals, comments,
  operators, and strings.

### Document Lifecycle
- `textDocument/didOpen`: stores the document text and logs a simple “Opened
  document …” message to the client.
- `textDocument/didChange`: updates the stored text using the last change in the
  change list (whole-document replacement only; no incremental merge yet).
- `textDocument/didClose`: removes the document from the store.
- Publishes diagnostics after each open/change/close event.

### Diagnostics
- Re-parses documents through `Parser::parse_from_src_with_diagnostics`.
- Runs the analyzer (`ModuleBuilder::build_from_src` + `InferSystem::infer_ty`)
  when the syntax phase succeeds so name/type errors surface alongside parser
  issues.
- Converts parser/analyzer `RayError`s into LSP diagnostics scoped to the
  current URI, falling back to parser errors if the standard library is
  unavailable. Toolchain discovery prefers the explicit `ray.toolchainPath`
  workspace setting, then `RAY_PATH`, the open workspace, `$HOME/.ray`, and
  finally `/opt/ray`; when no toolchain is found we log a warning so users know
  analyzer diagnostics are disabled.
- Sends diagnostics (and clears them on close) with the document version, so
  editors can track stale results.

### Semantic Tokens
- `textDocument/semanticTokens/full`:
  - Re-lexes the cached source using the compiler’s lexer (`ray::parse::lexer`).
  - Converts tokens (and doc comment trivia) into `SemanticToken`s using a small
    classifier.
  - Handles tokens that span multiple lines by truncating the text at the first
    newline before computing length (prevents mixing line offsets).
  - Unit-tested in `semantic_tokens::tests::classify_module_and_function_docs`.
  - Token types covered:
    - Keywords (`fn`, `struct`, modifiers, etc.)
    - Identifiers / prefixed identifiers treated as variables
    - Numeric literals (`Integer`, `Float`, `Bool`)
    - Comments (`//`, `///`, `//!`)
    - Operators and punctuation (covers most delimiter/operator tokens)
    - Strings (currently only Unicode escape sequences; string literal handling
      needs better support once the lexer exposes full spans)

## Not Implemented (Yet)

| Capability | Notes / Impact |
|------------|----------------|
| Analyzer enhancements | Surface related information, debounce expensive passes, and handle multi-file diagnostics gracefully. |
| Hover / go-to definition / completion | Requires wiring into the analyzer / name resolution structures. |
| Semantic tokens delta & range requests | We advertise `full` only; no delta/range support (both require caching previous results). |
| Partial edits (`didChange` incremental) | Currently replaces the entire text. Either adopt LSP incremental edits or shift to rope-based storage if we see perf problems. |
| Token modifiers | Everything uses a blank modifier bitset. Future work: surface doc comment vs regular comment, mutable variables, etc. |
| Strings & characters | The lexer emits quote tokens separately; add handling once we have string AST nodes via the parser. |
| Workspace-wide features | No project model, no configuration handling, no `didChangeConfiguration`. |

## Known Limitations / Technical Debt

- **Document Store**: naive `HashMap<Url, String>` may be a perf bottleneck on
  large files. We can switch to rope or incremental snapshot handling later.
- **Multi-line tokens**: the lexer reports span end past the newline for comment
  lines; we truncate manually. Ideally, the lexer would return spans that match
  the text that the editor should highlight.
- **Lexer dependency**: semantic tokens re-run the lexing each time. Once we
  have parser integration for diagnostics we may want to cache lexemes or reuse
  parser results.
- **Logging**: only initialization and didOpen message; no structured tracing or
  diagnostics logging.
- **Tests**: one smoke test in `semantic_tokens.rs`. Add more coverage for
  numbers/operators to avoid regressions.

## Suggested Next Steps

1. **Analyzer Diagnostics+**
   - Cache analyzer/front-end state so we do not rebuild the world on every
     change; explore incremental updates or cheap invalidation.
   - Enrich diagnostics with related locations (e.g. definition sites,
     conflicting spans) from the analyzer.
   - Handle multi-file results (imports, generated modules) without spamming
     open documents; consider surfacing summary notifications if the stdlib is
     missing.

2. **Expand Semantic Tokens**
   - Support doc comment modifiers (e.g., treat `//!` as module docs, `///` as
     documentation).
   - Classify string literals and character tokens once the lexer exposes the
     necessary spans.
   - Measure token data volume for large files (LSP max message size).

3. **Incremental Updates**
   - Handle `DidChangeTextDocumentContentChange` properly (range-based updates).
   - Implement `semanticTokens/full/delta` to avoid recomputing entire documents.

4. **Editor Integration**
   - Update the VS Code extension to request semantic tokens and to fall back to
     TextMate scopes if the server is unavailable.
   - Document configuration options (log level, feature flags) once we add them.

5. **Developer Tooling**
   - Add more unit tests covering the token classifier (numbers, operators,
     multiline strings).
   - Consider a golden-file test that round-trips semantic token responses for
     sample Ray programs.

## How to Run & Debug

From the workspace root:

```bash
cargo check -p ray-lsp                # type-check the server
cargo test  -p ray-lsp                # run ray-lsp unit tests
RUST_LOG=ray_lsp=debug cargo run -p ray-lsp
```

Attach the server to an editor via stdio, or use the `vscode-rust-analyzer`
style launch configs in the `editors/vscode/` directory when we add them.

## Filing Rough Edges / Future Ideas

- Hook into the Ray analyzer to offer basic completions (`with`, `import`,
  struct field names).
- Provide hover information (type signatures, doc comments).
- Implement go-to-definition using the symbol tables in `ray::collections`.
- Add configuration handling (`workspace/didChangeConfiguration`) to enable /
  disable experimental features.
- Investigate incremental parsing to speed up diagnostics and semantic token
  updates.

If you spot differences between this document and the behaviour in code, please
update the relevant sections – keeping this in sync will make future threads
much easier to spin up quickly.
