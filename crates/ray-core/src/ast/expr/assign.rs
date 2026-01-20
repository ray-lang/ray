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
    /// Checks if the LHS Pattern is a Name and returns true if it has a type annotation
    ///
    /// This doesn't take into account other patterns or nested patterns, which may
    /// also have type annotations. Consider changing this method if necessary, but
    /// for its current use, this logic is sufficient.
    pub fn is_annotated(&self) -> bool {
        match &self.lhs.value {
            Pattern::Name(name) => name.ty.is_some(),
            _ => {
                // this isn't entirely accurate, however it's good enough (see above)
                false
            }
        }
    }

    pub fn get_ty_span(&self) -> Option<Span> {
        if let Pattern::Name(n) = &self.lhs.value {
            n.ty.as_ref().and_then(|t| t.span().copied())
        } else {
            None
        }
    }
}
