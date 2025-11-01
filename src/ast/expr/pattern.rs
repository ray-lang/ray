use std::{convert::TryFrom, ops::Deref};

use crate::{
    ast::{Missing, Node, Path, PrefixOp},
    errors::{RayError, RayErrorKind},
    utils::join,
};

use super::{Expr, Name, Sequence};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(Name),
    Sequence(Vec<Node<Pattern>>),
    Tuple(Vec<Node<Pattern>>),
    Deref(Node<Name>),
    Missing(Missing),
}

impl TryFrom<Expr> for Pattern {
    type Error = RayError;

    fn try_from(expr: Expr) -> Result<Self, Self::Error> {
        match expr {
            Expr::Name(n) => Ok(Pattern::Name(n)),
            Expr::Tuple(tuple) => Pattern::tuple(tuple.seq),
            Expr::Sequence(seq) => Pattern::try_from(seq),
            Expr::UnaryOp(unop)
                if matches!(unop.op.deref(), PrefixOp::Deref)
                    && matches!(unop.expr.value, Expr::Name(_)) =>
            {
                let name = unop.expr.take_map(|expr| variant!(expr, if Expr::Name(n)));
                Ok(Pattern::Deref(name))
            }
            Expr::Deref(deref) if matches!(deref.expr.value, Expr::Name(_)) => {
                let name = deref.expr.take_map(|expr| variant!(expr, if Expr::Name(n)));
                Ok(Pattern::Deref(name))
            }
            _ => Err(RayError {
                kind: RayErrorKind::Parse,
                msg: format!("{} is an invalid pattern", expr.desc()),
                src: vec![],
                context: Some("pattern try_from conversion".to_string()),
            }),
        }
    }
}

impl TryFrom<Sequence> for Pattern {
    type Error = RayError;

    fn try_from(mut seq: Sequence) -> Result<Self, Self::Error> {
        if seq.items.len() == 1 {
            let item = seq.items.pop().unwrap();
            Pattern::try_from(item.value)
        } else {
            Ok(Pattern::Sequence(
                seq.items
                    .into_iter()
                    .map(|i| i.try_take_map(|i| Pattern::try_from(i)))
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
                Pattern::Missing(m) => format!("(missing {})", m),
            }
        )
    }
}

impl Pattern {
    pub fn tuple(seq: Sequence) -> Result<Self, RayError> {
        Ok(Pattern::Tuple(
            seq.items
                .into_iter()
                .map(|i| i.try_take_map(|i| Pattern::try_from(i)))
                .collect::<Result<_, _>>()?,
        ))
    }

    pub fn path(&self) -> Option<&Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(&n.path),
            Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => None,
        }
    }

    pub fn path_mut(&mut self) -> Option<&mut Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(&mut n.path),
            Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => None,
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(n.path.to_string()),
            Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => None,
        }
    }
}

impl Node<Pattern> {
    pub fn paths(&self) -> Vec<Node<(&Path, bool)>> {
        match &self.value {
            Pattern::Name(n) => vec![Node::with_id(self.id, (&n.path, false))],
            Pattern::Deref(n) => vec![Node::with_id(self.id, (&n.path, true))],
            Pattern::Tuple(ps) | Pattern::Sequence(ps) => {
                ps.iter().map(|p| p.paths()).flatten().collect()
            }
            Pattern::Missing(_) => vec![],
        }
    }

    pub fn paths_mut(&mut self) -> Vec<Node<(&mut Path, bool)>> {
        match &mut self.value {
            Pattern::Name(n) => vec![Node::with_id(self.id, (&mut n.path, false))],
            Pattern::Deref(n) => vec![Node::with_id(n.id, (&mut n.path, true))],
            Pattern::Tuple(ps) | Pattern::Sequence(ps) => {
                ps.iter_mut().map(|p| p.paths_mut()).flatten().collect()
            }
            Pattern::Missing(_) => vec![],
        }
    }
}
