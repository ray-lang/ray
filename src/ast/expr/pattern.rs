use std::{convert::TryFrom, ops::Deref};

use crate::{
    ast::{Node, Path, PrefixOp},
    errors::{RayError, RayErrorKind},
    utils::join,
};

use super::{Expr, Name, Sequence};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(Name),
    Sequence(Vec<Pattern>),
    Tuple(Vec<Pattern>),
    Deref(Name),
}

impl TryFrom<Node<Expr>> for Pattern {
    type Error = RayError;

    fn try_from(expr: Node<Expr>) -> Result<Self, Self::Error> {
        match expr.value {
            Expr::Name(n) => Ok(Pattern::Name(n)),
            Expr::Tuple(tuple) => Pattern::tuple(tuple.seq),
            Expr::Sequence(seq) => Pattern::try_from(seq),
            Expr::UnaryOp(unop)
                if matches!(unop.op.deref(), PrefixOp::Deref)
                    && matches!(unop.expr.value, Expr::Name(_)) =>
            {
                let name = variant!(unop.expr.value, if Expr::Name(n));
                Ok(Pattern::Deref(name))
            }
            _ => Err(RayError {
                kind: RayErrorKind::Parse,
                msg: format!("{} is an invalid pattern", expr.desc()),
                src: vec![],
            }),
        }
    }
}

impl TryFrom<Sequence> for Pattern {
    type Error = RayError;

    fn try_from(mut seq: Sequence) -> Result<Self, Self::Error> {
        if seq.items.len() == 1 {
            Pattern::try_from(seq.items.pop().unwrap())
        } else {
            Ok(Pattern::Sequence(
                seq.items
                    .into_iter()
                    .map(|i| Pattern::try_from(i))
                    .collect::<Result<_, _>>()?,
            ))
        }
    }
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Pattern::Name(n) => n.to_string(),
                Pattern::Sequence(seq) => join(seq, ", "),
                Pattern::Tuple(seq) => format!("(tuple ({}))", join(seq, ", ")),
                Pattern::Deref(n) => format!("(deref {})", n),
            }
        )
    }
}

impl Pattern {
    pub fn tuple(seq: Sequence) -> Result<Self, RayError> {
        Ok(Pattern::Tuple(
            seq.items
                .into_iter()
                .map(|i| Pattern::try_from(i))
                .collect::<Result<_, _>>()?,
        ))
    }

    pub fn path(&self) -> Option<&Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(n) => Some(&n.path),
            Pattern::Sequence(_) | Pattern::Tuple(_) => None,
        }
    }

    pub fn path_mut(&mut self) -> Option<&mut Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(n) => Some(&mut n.path),
            Pattern::Sequence(_) | Pattern::Tuple(_) => None,
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Pattern::Name(n) | Pattern::Deref(n) => Some(n.path.to_string()),
            Pattern::Sequence(_) | Pattern::Tuple(_) => None,
        }
    }
}
