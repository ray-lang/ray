use crate::{
    ast::{Expr, Node},
    span::{parsed::Parsed, Span},
    typing::ty::Ty,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct New {
    pub ty: Node<Parsed<Ty>>,
    pub count: Option<Box<Node<Expr>>>,
    pub new_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for New {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "new({}{})",
            self.ty,
            if let Some(count) = &self.count {
                format!(", {}", count)
            } else {
                str!("")
            }
        )
    }
}
