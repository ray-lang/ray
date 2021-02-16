use crate::utils::join;

use super::{Expr, Name, Sequence};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(Name),
    Sequence(Vec<Pattern>),
    Tuple(Vec<Pattern>),
}

impl From<Expr> for Pattern {
    fn from(expr: Expr) -> Self {
        match expr {
            Expr::Name(n) => Pattern::Name(n),
            Expr::Tuple(tuple) => Pattern::tuple(tuple.seq),
            Expr::Sequence(seq) => Pattern::from(seq),
            _ => unreachable!(),
        }
    }
}

impl From<Sequence> for Pattern {
    fn from(mut seq: Sequence) -> Self {
        if seq.items.len() == 1 {
            Pattern::from(seq.items.pop().unwrap().value)
        } else {
            Pattern::Sequence(
                seq.items
                    .into_iter()
                    .map(|i| Pattern::from(i.value))
                    .collect(),
            )
        }
    }
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match &self {
                Pattern::Name(n) => n.to_string(),
                Pattern::Sequence(seq) => join(seq, ", "),
                Pattern::Tuple(seq) => format!("(tuple ({}))", join(seq, ", ")),
            }
        )
    }
}

impl Pattern {
    pub fn tuple(seq: Sequence) -> Self {
        Pattern::Tuple(
            seq.items
                .into_iter()
                .map(|i| Pattern::from(i.value))
                .collect(),
        )
    }
}
