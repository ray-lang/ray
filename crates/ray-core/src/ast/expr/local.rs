use ray_typing::ty::Ty;

use crate::ast::{Expr, Node, Pattern};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Local {
    pub is_mut: bool,
    pub pattern: Box<Pattern>,
    pub ty: Option<Ty>,
    pub init: Option<Box<Node<Expr>>>,
}
