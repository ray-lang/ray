use std::{convert::TryFrom, ops::Deref};

use ray_shared::{pathlib::Path, span::Span, utils::join};
use serde::{Deserialize, Serialize};

use crate::{
    ast::{self, Missing, Node, PrefixOp, Tuple},
    errors::{RayError, RayErrorKind},
};

use super::{Expr, Name, Sequence};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern {
    Deref(Node<Name>),
    Dot(Box<Node<Pattern>>, Node<Name>),
    Index(Box<Node<Pattern>>, Box<Node<Expr>>, Span),
    Missing(Missing),
    Name(Name),
    Sequence(Vec<Node<Pattern>>),
    Some(Box<Node<Pattern>>),
    Tuple(Vec<Node<Pattern>>),
    /// A variant pattern in a match arm: `ok(v)`, `custom(r, g, b)`.
    /// The `Node<Path>` holds the variant constructor name with its own NodeId
    /// for name resolution. The `Vec` holds the payload bindings.
    Variant(Node<Path>, Vec<Node<Pattern>>),
    /// Wildcard pattern in a match arm: `_`. Matches any value, binds nothing.
    Wildcard,
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
            Pattern::Index(lhs, index, bracket_span) => Expr::Index(ast::Index {
                lhs: Box::new(lhs.take_map(Pattern::into)),
                index,
                bracket_span,
            }),
            Pattern::Missing(missing) => Expr::Missing(missing),
            Pattern::Some(inner) => {
                let expr = inner.take_map(Pattern::into);
                Expr::Some(Box::new(expr))
            }
            Pattern::Variant(_, _) | Pattern::Wildcard => {
                unreachable!(
                    "Variant and Wildcard patterns only appear in match arms, not in assignment patterns"
                )
            }
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
            Expr::Index(index) => {
                let lhs = index.lhs.try_take_map(|lhs| Pattern::try_from(lhs))?;
                Ok(Pattern::Index(
                    Box::new(lhs),
                    index.index,
                    index.bracket_span,
                ))
            }
            Expr::Some(inner) => {
                let pat = Pattern::try_from(inner.value)?;
                Ok(Pattern::Some(Box::new(Node::with_id(inner.id, pat))))
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
                Pattern::Index(lhs, index, _) => format!("(index {} {})", lhs, index),
                Pattern::Some(pat) => format!("(some {})", pat),
                Pattern::Missing(m) => format!("(missing {})", m),
                Pattern::Variant(name, fields) if fields.is_empty() => {
                    format!("(variant {})", name.value)
                }
                Pattern::Variant(name, fields) => {
                    format!("(variant {} ({}))", name.value, join(fields, ", "))
                }
                Pattern::Wildcard => "_".to_string(),
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
            Pattern::Some(inner) => inner.value.path(),
            Pattern::Variant(path, _) => Some(&path.value),
            Pattern::Index(_, _, _) | Pattern::Wildcard => None,
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }

    pub fn path_mut(&mut self) -> Option<&mut Path> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(&mut n.path),
            Pattern::Some(inner) => inner.value.path_mut(),
            Pattern::Variant(path, _) => Some(&mut path.value),
            Pattern::Index(_, _, _) | Pattern::Wildcard => None,
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }

    pub fn get_name(&self) -> Option<String> {
        match self {
            Pattern::Name(n) | Pattern::Deref(Node { id: _, value: n }) => Some(n.path.to_string()),
            Pattern::Some(inner) => inner.value.get_name(),
            Pattern::Variant(path, _) => path.value.name().map(|s| s.to_string()),
            Pattern::Index(_, _, _) | Pattern::Wildcard => None,
            Pattern::Dot(_, _) | Pattern::Sequence(_) | Pattern::Tuple(_) | Pattern::Missing(_) => {
                None
            }
        }
    }
}

pub struct PathBinding<'a> {
    pub path: &'a Path,
    pub is_bindable: bool,
}

impl<'a> PathBinding<'a> {
    pub fn new(path: &'a Path, is_bindable: bool) -> Self {
        Self { path, is_bindable }
    }
}

pub struct PathBindingMut<'a> {
    pub path: &'a mut Path,
    pub is_bindable: bool,
}

impl<'a> PathBindingMut<'a> {
    pub fn new(path: &'a mut Path, is_bindable: bool) -> Self {
        Self { path, is_bindable }
    }
}

impl Node<Pattern> {
    pub fn paths(&self) -> Vec<Node<PathBinding<'_>>> {
        match &self.value {
            Pattern::Name(n) => vec![Node::with_id(self.id, PathBinding::new(&n.path, true))],
            Pattern::Deref(n) => vec![Node::with_id(n.id, PathBinding::new(&n.path, false))],
            Pattern::Dot(lhs, n) => lhs
                .paths()
                .into_iter()
                .map(|mut node| {
                    node.is_bindable = false; // Mark LHS paths as NOT bindable
                    node
                })
                .chain(std::iter::once(Node::with_id(
                    n.id,
                    PathBinding::new(&n.path, false),
                )))
                .collect(),
            Pattern::Index(lhs, _, _) => match &lhs.value {
                Pattern::Name(n) => vec![Node::with_id(lhs.id, PathBinding::new(&n.path, false))],
                Pattern::Deref(n) => vec![Node::with_id(lhs.id, PathBinding::new(&n.path, false))],
                _ => lhs.paths(),
            },
            Pattern::Some(inner) => inner.paths(),
            Pattern::Tuple(ps) | Pattern::Sequence(ps) => {
                ps.iter().flat_map(|p| p.paths()).collect()
            }
            Pattern::Missing(_) => vec![],
            // Variant: only the sub-pattern bindings are local bindings; the
            // constructor path is resolved separately during name resolution.
            Pattern::Variant(_, sub_patterns) => {
                sub_patterns.iter().flat_map(|p| p.paths()).collect()
            }
            Pattern::Wildcard => vec![],
        }
    }

    pub fn paths_mut(&mut self) -> Vec<Node<PathBindingMut<'_>>> {
        match &mut self.value {
            Pattern::Name(n) => vec![Node::with_id(
                self.id,
                PathBindingMut::new(&mut n.path, true),
            )],
            Pattern::Deref(n) => vec![Node::with_id(n.id, PathBindingMut::new(&mut n.path, false))],
            Pattern::Dot(lhs, n) => lhs
                .paths_mut()
                .into_iter()
                .map(|mut node| {
                    node.is_bindable = false; // Mark LHS paths as NOT bindable
                    node
                })
                .chain(std::iter::once(Node::with_id(
                    n.id,
                    PathBindingMut::new(&mut n.path, false),
                )))
                .collect(),
            Pattern::Index(lhs, _, _) => lhs
                .paths_mut()
                .into_iter()
                .map(|mut node| {
                    node.is_bindable = false;
                    node
                })
                .collect(),
            Pattern::Some(inner) => inner.paths_mut(),
            Pattern::Tuple(ps) | Pattern::Sequence(ps) => {
                ps.iter_mut().flat_map(|p| p.paths_mut()).collect()
            }
            Pattern::Missing(_) => vec![],
            Pattern::Variant(_, sub_patterns) => sub_patterns
                .iter_mut()
                .flat_map(|p| p.paths_mut())
                .collect(),
            Pattern::Wildcard => vec![],
        }
    }
}
