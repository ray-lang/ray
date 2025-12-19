# IDE Identifiers: `NodeId` vs `Path`

This document codifies when IDE/LSP features should use `NodeId` versus `Path`.

## Definitions

- `NodeId`: Identity of a specific AST node in a specific compilation/snapshot.
  - Precise for a particular source position.
  - Correct under local shadowing (two different `x` bindings have different `NodeId`s).
  - Not stable across runs/builds and not meaningful outside the snapshot that produced it.

- `Path`: A stable, name-based identifier in Ray's namespace (for example `core::list::get`).
  - Stable across builds as long as the symbol's name/module path stays the same.
  - Suitable for cross-module indexing and serialized artifacts.
  - Not precise for locals (shadowed locals intentionally share the same path).

## Use `NodeId` for occurrences

Use `NodeId` when answering questions about "the thing at this position in this file right now".

Typical uses:
- Hover type for an identifier/expression under the cursor.
- Semantic tokens classification for a particular token occurrence.
- Intra-module diagnostics keyed to an exact AST node.
- Any local-identity-sensitive behavior (shadowing, pattern binders, etc.).

Do not use `Path` for these, because locals can intentionally collide by name.

## Use `Path` for stable definitions

Use `Path` when referring to a definition in a way that must be stable across builds and shareable
across modules and artifacts.

Typical uses:
- `.raylib` definition indexing (exported API surface).
- Cross-module symbol search and indexing.
- Linking/import resolution and any persistent caches.

Do not use `NodeId` as a key for persisted/cross-module data; it is snapshot-local and can change
between runs.

## Recommended LSP pipeline (dual-keyed)

Most IDE features should start from `NodeId` (cursor location), then choose the right key based on
what is being answered.

- Hover type:
  - Use `NodeId -> type` from the snapshot.
  - Do not go through `Path` for locals.

- Hover docs/signature:
  - If the target is a local occurrence, use snapshot data keyed by `NodeId`.
  - If the target is a global/exported symbol, use `Path -> DefinitionRecord` for stable docs.

- Go-to-definition:
  - Preferred: `NodeId(usage) -> Path -> DefinitionRecord(file/span)` for cross-module jumps.
  - Optional optimization: for purely local definitions, a direct `NodeId(usage) -> location`
    mapping can avoid path-based ambiguity.

## Rule of thumb

- Use `NodeId` for occurrences.
- Use `Path` for stable, cross-module definitions.

