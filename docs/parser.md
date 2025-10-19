# Ray Parser

This document sketches the organisation of the Ray language parser, the error-
recovery strategy it employs, and the data structures involved. It is intended
for contributors who need to extend the grammar or debug recovery behaviour.

## High-level pipeline

Parsing is anchored in `src/parse/parser`. The key stages are:

1. **Lexical analysis** – `parse::lexer::Lexer` produces a token stream. The
   parser always works on a `Lexer` instance; no tokens are materialised in
   advance.
2. **Parser façade (`Parser`)** – `Parser` coordinates parsing, owns the lexer,
   collects diagnostics, and populates the `SourceMap` with spans/doc comments.
3. **Grammar modules** – the `parser` directory fan-outs into submodules for
   distinct syntactic areas:
   - `atoms.rs` – primitives (blocks, literals, paths, closures …)
   - `expr.rs` / `control.rs` – expression grammar and control-flow constructs
   - `decl.rs` / `func.rs` – declarations and function signatures/bodies
   - `ty.rs` – type grammar
   - `collections.rs`, `imports.rs`, `ops.rs` – specialised helpers
4. **AST construction** – the parser emits `Typed` AST nodes (`Node<T>`). The
   `SourceMap` is updated via helpers like `mk_expr`, ensuring diagnostics can
   be mapped back to source.
5. **Constraint collection / semantic passes** – downstream crates (`ast`,
   `typing`, `sema`) consume the AST. Although not part of the parser, they
   rely on consistent placeholder nodes when the parser recovers.

`Parser::parse_*` methods are generally split by syntactic domain, with the
module structure mirroring the AST hierarchy.

## Parser context

`ParseContext` carries persistent flags across recursive calls:

- `path`: current module/function path; used by `SourceMap`.
- `restrictions`: a `bitflags` set that forbids constructs (e.g. `NO_CURLY_EXPR`
  when expressions appear in contexts where `{}` would be ambiguous).
- `stop_token`: optionally instructs sub-parsers to bail when a particular
  token is encountered (used for recovery loops).
- `in_func` / `in_loop` / `top_level`: state bits that inform statement parsing.

Contexts are usually cloned and tweaked before delegating to sub-parsers.

## Diagnostics & recovery

### Recording errors

`Parser::record_parse_error` appends a `RayError` to the parser’s `errors`
vector. All parse errors are non-fatal: the parser attempts to continue to
produce an AST decorated with `Missing` placeholders.

### `Missing` nodes

To avoid ambiguity with real syntax, the parser never fabricates concrete
expressions/patterns. Instead it creates:

- `Expr::Missing(Missing { expected, context })`
- `Pattern::Missing(Missing { expected, context })`

`expected` describes what the parser was looking for (e.g. `"block"` or
`"expression"`). `context` is derived from the current `ParseContext.path`.
Downstream passes check these variants to skip semantic work or emit follow-up
diagnostics.

### `Recover` trait

`src/parse/parser/recover.rs` defines a `Recover<T>` trait implemented for
`Result<T, RayError>`. Its `recover_with` method wraps the common pattern of:

1. Attempting a parse function (`Result<T, RayError>`).
2. On `Err`, record the error, call `recover_after_error` to advance the lexer,
   and construct a placeholder via a callback.

Usage example:

```rust
let cond = self
    .parse_pre_block_expr(ctx)
    .recover_with(self, Some(&TokenKind::LeftCurly), |parser, recovered| {
        parser.missing_expr(cond_start, recovered, ctx)
    });
```

The optional `stop` token ensures the recovery loop stops at a reasonable point
(`recover_after_error` rewinds to safe boundaries such as `}` or EOF).

### Manual recovery helpers

Some constructs still manage recovery directly (notably sequences in `atoms.rs`
and `ty.rs`). These rely on:

- `Parser::recover_after_error(stop_token)` – advances token-by-token, tracking
  nesting until a recovery point (stop token, `}`, `EOF`, newline, or next
  declaration start) is found.
- `Parser::recover_after_sequence_error(stop_token)` – specialised for comma-
  separated lists.

Legacy code emits `_` placeholders or empty nodes; ongoing work is migrating
remaining sites to use the `Missing` variants via `recover_with`.

## Tests

Parser tests reside at the bottom of `parser/mod.rs`. They feed small snippets
into `Parser::parse_from_src_with_diagnostics`, asserting that:

- Recovery produces ASTs containing `Missing` nodes where expected.
- Diagnostics include `RayErrorKind::Parse` entries pointing at the offending
  spans.
- Doc comments are preserved (see the doc-comment tests).

These tests are invaluable when altering recovery behaviour—ensure new recovery
paths also update or add tests to confirm placeholder content.

## Extending the parser

When adding grammar rules or recovery logic:

1. Evaluate whether the construct fits an existing module or warrants a new
   sub-module under `parser/`.
2. Carry the `ParseContext` forward, adjusting restrictions as needed.
3. Use `recover_with` for optional constructs so recovery is consistent with the
   rest of the parser.
4. Populate the `SourceMap` for any new AST nodes via `mk_expr`, `mk_decl`, etc.
5. Add targeted tests in `parser/mod.rs` verifying both success and recovery
   scenarios.

By keeping placeholders explicit (`Missing`), downstream passes can either skip
or tailor diagnostics without confusing parsed-but-invalid AST nodes with real
syntax.
