use crate::ast::Expr;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct If {
    pub cond: Box<Expr>,
    pub then: Box<Expr>,
    pub els: Option<Box<Expr>>,
}

impl std::fmt::Display for If {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let els = if let Some(ref els) = self.els {
            format!(" else {}", els)
        } else {
            String::new()
        };
        write!(f, "(if {} {}{})", self.cond, self.then, els,)
    }
}
