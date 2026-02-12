use ray_shared::{
    span::{Span, parsed::Parsed},
    ty::Ty,
};
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Cast {
    pub lhs: Box<Node<Expr>>,
    pub ty: Parsed<Ty>,
    pub as_span: Span,
}

impl std::fmt::Display for Cast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(cast {} as {})", self.lhs, self.ty)
    }
}
