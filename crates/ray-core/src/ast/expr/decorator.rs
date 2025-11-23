use ray_shared::{pathlib::Path, utils::join};
use serde::{Deserialize, Serialize};

use crate::ast::Node;
use ray_shared::span::Span;

use super::Name;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Decorator {
    pub path: Node<Path>,
    pub args: Vec<Node<Name>>,
    pub paren_sp: Option<Span>,
}

impl std::fmt::Display for Decorator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}({})", self.path, join(&self.args, ", "))
    }
}
