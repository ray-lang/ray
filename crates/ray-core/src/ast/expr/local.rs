use ray_shared::ty::Ty;
use serde::{Deserialize, Serialize};

use crate::ast::{Expr, Node, Pattern};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Local {
    pub is_mut: bool,
    pub pattern: Box<Pattern>,
    pub ty: Option<Ty>,
    pub init: Option<Box<Node<Expr>>>,
}
