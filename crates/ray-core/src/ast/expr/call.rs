use ray_shared::{node_id::NodeId, span::Span};
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node, Sequence};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Call {
    pub callee: Box<Node<Expr>>,
    pub args: Sequence,
    pub args_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for Call {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.items.len() == 0 {
            write!(f, "(call {})", self.callee)
        } else {
            write!(f, "(call {} {})", self.callee, self.args)
        }
    }
}

impl Call {
    pub fn new(callee: Node<Expr>, args: Vec<Node<Expr>>) -> Self {
        Self {
            callee: Box::new(callee),
            args: Sequence::new(args),
            args_span: Span::new(),
            paren_span: Span::new(),
        }
    }

    pub fn call_resolution_id(&self) -> NodeId {
        // call_resolution expects id of either:
        //  - the name node of the callee in dot (`f` in `e.f`)
        //  - or the callee node itself
        if let Expr::Dot(dot) = &self.callee.value {
            dot.rhs.id
        } else {
            self.callee.id
        }
    }

    pub fn is_method_call(&self) -> bool {
        // Non-static method calls can only be made through a Dot operation
        matches!(self.callee.value, Expr::Dot(_))
    }
}
