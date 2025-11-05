//! IDE-facing utilities (semantic tokens, source navigation, etc.).
//!
//! This module is intentionally lightweight for now.  The goal is to keep
//! presentation-layer helpers out of the core parser / typer crates while still
//! reusing the existing AST and `SourceMap`.

pub mod semantic_tokens;
