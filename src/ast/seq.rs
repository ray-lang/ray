use crate::ast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sequence {
    pub items: Vec<ast::Expr>,
    pub trailing: bool, // trailing comma
}

impl Sequence {
    pub fn empty() -> Sequence {
        Sequence {
            items: vec![],
            trailing: false,
        }
    }
}

impl std::fmt::Display for Sequence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.items.len() == 0 {
            write!(f, "(seq)")
        } else {
            write!(
                f,
                "(seq {})",
                self.items
                    .iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
    }
}
