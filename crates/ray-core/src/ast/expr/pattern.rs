use std::{convert::TryFrom, ops::Deref};

use ray_shared::{pathlib::Path, utils::join};

use ray_shared::span::Span;
use crate::{
    ast::{self, Missing, Node, PrefixOp, Tuple},
    errors::{RayError, RayErrorKind},
};

use super::{Expr, Name, Sequence};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pattern {
    Name(Name),
    Sequence(Vec<Node<Pattern>>),
    Tuple(Vec<Node<Pattern>>),
    Deref(Node<Name>),
    Dot(Box<Node<Pattern>>, Node<Name>),
    Missing(Missing),
}

impl Into<Expr> for Pattern {
    fn into(self) -> Expr {
        match self {
            Pattern::Name(name) => Expr::Name(name),
            Pattern::Sequence(nodes) => Expr::Sequence(Sequence {
                items: nodes
                    .into_iter()
                    .map(|node| node.take_map(Pattern::into))
                    .collect(),
                trailing: false,
            }),
            Pattern::Tuple(nodes) => Expr::Tuple(Tuple {
                seq: Sequence {
                    items: nodes
                        .into_iter()
                        .map(|node| node.take_map(Pattern::into))
                        .collect(),
                    trailing: false,
                },
            }),
            Pattern::Deref(node) => Expr::Deref(ast::Deref {
                expr: Box::new(node.take_map(Expr::Name)),
                op_span: Span::new(),
            }),
            Pattern::Dot(lhs, rhs) => Expr::Dot(ast::Dot {
                lhs: Box::new(lhs.take_map(Pattern::into)),
                rhs,
                dot: ast::token::Token {
                    kind: ast::token::TokenKind::Dot,
                    span: Span::new(),
                },
            }),
            Pattern::Missing(missing) => Expr::Missing(missing),
        }
    }
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
            Expr::Dot(dot) => {
                let lhs = dot.lhs.try_take_map(|lhs| Pattern::try_from(lhs))?;
                Ok(Pattern::Dot(Box::new(lhs), dot.rhs))
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
                Pattern::Dot(lhs, name) => format!("(dot {}.{})", lhs, name),
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
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }

    pub fn path_mut(&mut self) -> Option<&mut Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(&mut n.path),
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(n.path.to_string()),
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }
}

impl Node<Pattern> {
    pub fn paths(&self) -> Vec<Node<(&Path, bool)>> {
        match &self.value {
            Pattern::Name(n) => vec![Node::with_id(self.id, (&n.path, false))],
            Pattern::Deref(n) => vec![Node::with_id(self.id, (&n.path, true))],
            Pattern::Dot(lhs, n) => lhs
                .paths()
                .into_iter()
                .chain(std::iter::once(Node::with_id(n.id, (&n.path, true))))
                .collect(),
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
            Pattern::Dot(lhs, n) => lhs
                .paths_mut()
                .into_iter()
                .chain(std::iter::once(Node::with_id(n.id, (&mut n.path, true))))
                .collect(),
            Pattern::Tuple(ps) | Pattern::Sequence(ps) => {
                ps.iter_mut().map(|p| p.paths_mut()).flatten().collect()
            }
            Pattern::Missing(_) => vec![],
        }
    }
}
