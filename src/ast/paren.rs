use crate::ast::Expr;

#[derive(Debug)]
pub struct Paren(pub Box<Expr>);

impl std::fmt::Display for Paren {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})", self.0)
    }
}
