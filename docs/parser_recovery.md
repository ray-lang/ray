# Parser Recovery Contract

## Objectives
1. **Correctness and determinism:** Recovery always makes forward progress. No infinite loops.
2. **Local damage only:** Keep bad tokens local. Preserve surrounding structure so later statements still parse.
3. **Ownership of closers:** A recovery routine never consumes the closing token owned by its caller.
4. **Clear diagnostics:** One primary error per fault. Optional notes only when helpful.
5. **Predictable AST:** Insert explicit Missing nodes instead of half-formed nodes.

## Token classes
- **Delimiters:** `(` `)` `[` `]` `{` `}`
- **Terminators:** newline, `;`
- **Separators:** `,`
- **Decl starters:** `fn, struct, trait, enum, type, impl, extern, object, import`

## Newline semantics
- Newline at depth 0 ends a statement.
- Newlines inside `()` and `[]` do not end a list.
- Newlines inside `{}` depend on construct:
  - Block body: newline can separate statements.
  - Curly expression or literal: newline is ignored for list separation unless followed by `,`.

## Invariants
- A recovery routine never consumes the caller stop token.
- Right closers are left for the caller that owns the opener.
- Sequence recovery may consume at most one `,` to advance a slot, never more than one in a row.
- Depth is tracked per delimiter class. Only matching closers affect that depth.
- Progress is measured by byte offset. If the offset does not change, consume one token unless at EOF, then return.

## Placeholders
- Missing expression: `Expr::Missing` via `missing_expr`
- Missing pattern: `Pattern::Missing` via `missing_pattern`
- Missing type: `Ty::Never` wrapped in `TyScheme` via `missing_type`
- Missing block: `missing_block_expr`

## Recovery context

Each recovery entry point receives a `RecoveryCtx` describing the mode-specific
rules it should obey. The context keeps delimiter ownership and newline policy
explicit so every call site can state what "forward progress" means for that
construct.

```rust
enum RecoveryMode {
    Stmt {
        newline_breaks: bool,    // newline at depth 0 ends the statement
        decl_stops: bool,        // stop when the next token starts a decl
    },
    Seq {
        delimiter: Delimiter,    // Paren | Bracket | Curly
        trailing: TrailingPolicy,// Allow | Warn | Forbid
        newline_breaks: bool,    // newline at depth 0 ends the element
    },
    Expr {
        ternary_sensitive: bool, // stop before else / ternary markers
        last_op: Option<InfixOp>,// operator we just consumed, if any
    },
}

struct RecoveryCtx<'a> {
    mode: RecoveryMode,
    stop: Option<&'a TokenKind>,   // caller-specific hard stop token
}
```

Legacy helper wrappers (`recover_after_error`, `recover_after_sequence_error`)
construct a context with sensible defaults so existing call sites keep working.
New or migrated sites should pass the richer `RecoveryCtx` so newline behavior,
declaration stops, and delimiter ownership remain explicit.

## Recovery modes

### 1) Statement recovery
**Purpose:** resync within a block after a failed statement.

**Stop set:**
- Caller stop token (optional)
- EOF
- Right curly at depth 0
- Newline or `;` at depth 0 when `newline_breaks = true`
- Any declaration starter at depth 0 when `decl_stops = true`

**Rules:**
- Do not consume the caller stop token.
- If at newline or `;` at depth 0, consume exactly one and stop.
- If at right curly at depth 0, stop without consuming.
- Otherwise consume tokens, updating delimiter depth, until a stop is encountered at depth 0.
- Progress check each loop iteration. If no progress, consume one token and stop.

**Result:** caller resumes at a statement boundary. Use a Missing node if needed.

### 2) Sequence recovery
**Purpose:** resync inside comma lists within `()` `[]` `{}`.

**Stop set:**
- Caller stop token (optional)
- EOF
- Right paren, right bracket, right curly at depth 0
- Newline at depth 0 when `newline_breaks = true`

**Rules:**
- If at `,` at depth 0 and have not consumed anything in this recovery, consume exactly one `,`, then stop. Record a note when the trailing policy forbids the comma.
- Do not consume right closers or newline. Leave them for the caller.
- Otherwise consume tokens, updating depth, until hitting a stop at depth 0.
- Progress check each iteration. If no progress, consume one token and stop.

**Result:** caller can insert a Missing element and either continue (if a comma was consumed) or close the list.

### 3) Expression recovery
**Purpose:** break out of a mid-expression failure, especially binary or ternary chains.

**Stop set:**
- Caller stop token (optional)
- EOF
- `,` newline `;` right paren, right bracket, right curly at depth 0
- `else` / ternary markers when `ternary_sensitive = true`

**Rules:**
- If parked on a binary operator with no RHS progress, consume exactly one operator (using `last_op` to emit the right diagnostic) and stop. This prevents op-op oscillation.
- Otherwise consume until a stop at depth 0. Track depth as usual.
- Progress check. If no progress, consume one token and stop.

**Result:** caller replaces the missing subexpression with a Missing expression and resumes at a safe boundary.

## APIs

### Parser primitives
```rust
// utility
fn progress_advanced(&mut self, last: &mut usize) -> bool;

// recovery
fn recover_stmt(&mut self, stop: Option<&TokenKind>);
fn recover_seq(&mut self, stop: Option<&TokenKind>);
fn recover_expr(&mut self, stop: Option<&TokenKind>);

// legacy wrappers to avoid churn at call sites
fn recover_after_error(&mut self, stop: Option<&TokenKind>) -> Pos;      // calls recover_stmt, returns current position
fn recover_after_sequence_error(&mut self, stop: Option<&TokenKind>);    // calls recover_seq
```

### Ergonomic adapters (existing trait kept)
```rust
trait Recover<T> {
    fn recover_with(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>, Pos) -> T,
    ) -> T;

    fn recover_seq(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>) -> T,
    ) -> T;
}

// Implementation delegates to recover_after_error and recover_after_sequence_error.
```

### Call site contracts

- **Top-level items and block statements**
  - Wrap each statement parse in `recover_with(..., stop = None, fallback = missing_expr or missing_pattern as needed)`.
  - Parser owns `}` for the block. Statement recovery must not consume it.

- **Lists inside delimiters** (args, tuple, array, generics, struct literal fields)
  - Use a sequence-aware entry point that parses elements one by one.
  - Each element parse uses `.recover_seq(...)` with `stop = RightParen|RightBracket|RightCurly`.
  - Allow or forbid trailing comma per construct.

- **Infix or ternary chains**
  - When parsing RHS, wrap with `recover_expr` behavior at the parser level or introduce an adapter if needed later.
  - Do not consume closers. Let the caller close delimiters.

- **Curly literal vs block**
  - Curly literal: list parsing rules. Newline does not end the list by itself unless followed by `,` or end.
  - Block: statement parsing rules. Newline ends statements at depth 0.

## Diagnostics

- Emit one primary error at the fault point.
- Add a note only when a comma or operator was auto-consumed to continue.
- Anchor spans from the most helpful token near the failure (often the operator or the opener).

## Progress guarantee

- Each recovery loop keeps a `last_offset`.
- If the lex position does not move, forcibly consume one token unless at EOF, then return.
- This guarantees termination even if upstream code has a logic bug.

## Testing

1. Statement error recovers at newline and parses the next statement.
2. Missing list item between commas produces one error and keeps parsing later elements.
3. Missing closing delimiter: sequence recovery stops at the closer and lets caller handle it.
4. Missing RHS of a binary op: one error, no spin, Missing expression inserted.
5. Newline handling inside lists vs blocks.
6. Recovery does not consume the caller stop token.
7. Deeply nested delimiters with an inner error do not break outer structure.
