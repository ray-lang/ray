use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

/// A single segment of an f-string.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FStringPart {
    /// A literal string segment (escapes already resolved).
    Literal(String),
    /// An interpolated expression inside `{...}`.
    Expr(Node<Expr>),
}

/// An f-string expression, e.g. `f"hello {name}"`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FString {
    pub parts: Vec<FStringPart>,
}

impl std::fmt::Display for FString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f\"")?;
        for part in &self.parts {
            match part {
                FStringPart::Literal(s) => write!(f, "{}", s)?,
                FStringPart::Expr(expr) => write!(f, "{{{}}}", expr)?,
            }
        }
        write!(f, "\"")
    }
}
