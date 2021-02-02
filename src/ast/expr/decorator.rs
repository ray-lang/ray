use crate::{ast, span::Span, utils::join};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decorator {
    pub path: ast::Path,
    pub args: Vec<ast::Name>,
    pub paren_sp: Span,
}

impl std::fmt::Display for Decorator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}({})", self.path, join(&self.args, ", "))
    }
}
