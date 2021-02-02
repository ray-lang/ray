use std::collections::HashSet;

use crate::ast::Node;

use super::{CurlyElementKind, Expr};

pub trait GetVars {
    fn get_vars(&self) -> HashSet<&String>;
}

impl<T> GetVars for Vec<T>
where
    T: GetVars,
{
    fn get_vars(&self) -> HashSet<&String> {
        self.iter().flat_map(|t| t.get_vars()).collect()
    }
}

impl<T, Info> GetVars for Node<T, Info>
where
    T: GetVars,
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn get_vars(&self) -> HashSet<&String> {
        self.value.get_vars()
    }
}

impl<Info> GetVars for Expr<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn get_vars(&self) -> HashSet<&String> {
        match self {
            Expr::Assign(a) => {
                let mut vars = a.lhs.get_vars();
                vars.extend(a.rhs.get_vars());
                vars
            }
            Expr::BinOp(b) => {
                let mut vars = b.lhs.get_vars();
                vars.extend(b.rhs.get_vars());
                vars
            }
            Expr::Block(b) => b.stmts.get_vars(),
            Expr::Break(b) => {
                if let Some(b) = b {
                    b.get_vars()
                } else {
                    HashSet::new()
                }
            }
            Expr::Call(c) => {
                let mut vars = c.lhs.get_vars();
                vars.extend(c.args.items.get_vars());
                vars
            }
            Expr::Cast(c) => c.lhs.get_vars(),
            Expr::Closure(c) => c.body.get_vars(),
            Expr::Curly(c) => {
                todo!()
            }
            Expr::DefaultValue(_) => todo!(),
            Expr::Dot(_) => todo!(),
            Expr::Fn(_) => todo!(),
            Expr::For(_) => todo!(),
            Expr::If(_) => todo!(),
            Expr::Index(_) => todo!(),
            Expr::Labeled(_, _) => todo!(),
            Expr::List(_) => todo!(),
            Expr::Literal(_) => todo!(),
            Expr::Loop(_) => todo!(),
            Expr::Name(_) => todo!(),
            Expr::Path(_) => todo!(),
            Expr::Paren(_) => todo!(),
            Expr::Range(_) => todo!(),
            Expr::Return(_) => todo!(),
            Expr::Sequence(_) => todo!(),
            Expr::Tuple(_) => todo!(),
            Expr::Type(_) => todo!(),
            Expr::TypeAnnotated(..) => todo!(),
            Expr::UnaryOp(_) => todo!(),
            Expr::Unsafe(_) => todo!(),
            Expr::While(_) => todo!(),
            Expr::Asm(_) => HashSet::new(),
        }
    }
}
