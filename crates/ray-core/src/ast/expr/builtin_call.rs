use ray_shared::span::Span;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum BuiltinKind {
    /// `freeze(expr)` — converts `*mut T` to `*T`
    Freeze,
    /// `id(expr)` — converts `*T` to `id *T`
    Id,
    /// `upgrade(expr)` — converts `id *T` to `nilable[*T]`
    Upgrade,
}

impl std::fmt::Display for BuiltinKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuiltinKind::Freeze => write!(f, "freeze"),
            BuiltinKind::Id => write!(f, "id"),
            BuiltinKind::Upgrade => write!(f, "upgrade"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct BuiltinCall {
    pub kind: BuiltinKind,
    pub arg: Box<Node<Expr>>,
    pub keyword_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for BuiltinCall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}({})", self.kind, self.arg)
    }
}
