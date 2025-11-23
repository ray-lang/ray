use ray_shared::span::Span;

use crate::ast::{Expr, InfixOp, Node, Pattern};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Assign {
    pub lhs: Node<Pattern>,
    pub rhs: Box<Node<Expr>>,
    pub is_mut: bool,
    pub mut_span: Option<Span>,
    pub op: InfixOp,
    pub op_span: Span,
}

impl std::fmt::Display for Assign {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(assign{} {} {} {})",
            if self.is_mut { " mut" } else { "" },
            self.lhs,
            self.op,
            self.rhs,
        )
    }
}

impl Assign {
    pub fn get_ty_span(&self) -> Option<Span> {
        if let Pattern::Name(n) = &self.lhs.value {
            n.ty.as_ref().and_then(|t| t.span().copied())
        } else {
            None
        }
    }
}
