use ray_shared::{
    span::{Span, parsed::Parsed},
    ty::Ty,
};
use serde::{Deserialize, Serialize};

use crate::ast::Node;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct New {
    pub ty: Node<Parsed<Ty>>,
    pub new_span: Span,
    pub paren_span: Span,
}

impl std::fmt::Display for New {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "new({})", self.ty)
    }
}
