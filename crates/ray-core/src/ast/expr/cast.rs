use crate::{
    ast::{Expr, Node},
    span::{Span, parsed::Parsed},
    typing::ty::Ty,
};

#[derive(Clone, Debug, PartialEq, Eq)]
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
