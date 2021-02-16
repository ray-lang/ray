use std::ops::DerefMut;

use crate::{
    ast::{Assign, Expr, Fn, FnSig, Name, Node, TypeParams},
    span::parsed::Parsed,
    strutils,
    typing::ty::Ty,
    utils::join,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Extern {
    decl: Box<Node<Decl>>,
    src: Option<String>,
}

impl std::fmt::Display for Extern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.decl)
    }
}

impl Extern {
    pub fn new(decl: Node<Decl>) -> Self {
        Self {
            decl: Box::new(decl),
            src: None,
        }
    }

    pub fn decl(&self) -> &Decl {
        &self.decl
    }

    pub fn decl_mut(&mut self) -> &mut Decl {
        self.decl.deref_mut()
    }

    pub fn src(&self) -> &Option<String> {
        &self.src
    }

    pub fn src_mut(&mut self) -> &mut Option<String> {
        &mut self.src
    }

    pub fn take(self) -> (Node<Decl>, Option<String>) {
        (*self.decl, self.src)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    Extern(Extern),
    Mutable(Node<Name>),
    Name(Node<Name>),
    Declare(Assign),
    Fn(Fn),
    FnSig(FnSig),
    Struct(Struct),
    Trait(Trait),
    TypeAlias(Node<Name>, Parsed<Ty>),
    Impl(Impl),
}

impl PartialOrd for Decl {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let i: usize = self.into();
        let j: usize = other.into();
        i.partial_cmp(&j)
    }
}

impl Ord for Decl {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let i: usize = self.into();
        let j: usize = other.into();
        i.cmp(&j)
    }
}

impl Into<usize> for &Decl {
    fn into(self) -> usize {
        match self {
            Decl::Trait(_) => 0,
            Decl::Struct(_) => 1,
            Decl::TypeAlias(_, _) => 2,
            Decl::Extern(_) => 3,
            Decl::Fn(_) | Decl::FnSig(_) => 4,
            Decl::Impl(_) => 5,
            Decl::Declare(_) => 6,
            Decl::Mutable(_) | Decl::Name(_) => 7,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Struct {
    pub name: Node<Name>,
    pub ty_params: Option<TypeParams>,
    pub fields: Option<Vec<Node<Name>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trait {
    pub ty: Parsed<Ty>,
    pub funcs: Vec<FnSig>,
    pub super_trait: Option<Parsed<Ty>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Impl {
    pub ty: Parsed<Ty>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub externs: Option<Vec<Node<Decl>>>,
    pub funcs: Option<Vec<Node<Decl>>>,
    pub consts: Option<Vec<Node<Expr>>>,
}

impl std::fmt::Display for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Extern(ext) => write!(f, "(extern {})", ext),
            Decl::Mutable(n) => write!(f, "(mut {})", n),
            Decl::Name(n) => write!(f, "(declare {})", n),
            Decl::Declare(a) => write!(f, "(declare {})", a),
            Decl::TypeAlias(n, ty) => write!(f, "(type {} = {})", n, ty),
            Decl::Fn(func) => write!(f, "{}", func),
            Decl::FnSig(sig) => write!(f, "(fn {})", sig),
            Decl::Struct(st) => {
                let tp = if let Some(tp) = &st.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                if let Some(fields) = &st.fields {
                    let fields = format!("{}\n", strutils::indent_lines_iter(fields, 2));
                    write!(f, "(struct {}{} {{\n{}}})", st.name, tp, fields)
                } else {
                    write!(f, "(struct {}{})", st.name, tp)
                }
            }
            Decl::Trait(tr) => {
                if tr.funcs.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&tr.funcs, 2));
                    write!(f, "(trait {}\n{})", tr.ty, methods)
                } else {
                    write!(f, "(trait {}\n)", tr.ty)
                }
            }
            Decl::Impl(im) => {
                let qualifiers = if im.qualifiers.len() != 0 {
                    format!("where {}", join(&im.qualifiers, ", "))
                } else {
                    str!("")
                };

                let funcs = if let Some(funcs) = &im.funcs {
                    let s = format!("{}", strutils::indent_lines_iter(funcs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let externs = if let Some(externs) = &im.externs {
                    let s = format!("{}", strutils::indent_lines_iter(externs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let consts = if let Some(consts) = &im.consts {
                    let s = format!("{}", strutils::indent_lines_iter(consts, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                if funcs.len() != 0 || externs.len() != 0 || consts.len() != 0 {
                    write!(
                        f,
                        "(impl {}{}\n{}{}{})",
                        im.ty, qualifiers, externs, consts, funcs
                    )
                } else {
                    write!(f, "(impl {}{})", im.ty, qualifiers)
                }
            }
        }
    }
}

impl Decl {
    pub fn get_name(&self) -> Option<String> {
        match &self {
            Decl::Extern(e) => e.decl.get_name(),
            Decl::Mutable(n) | Decl::Name(n) => Some(n.path.to_string()),
            Decl::Fn(f) => f.sig.name.clone(),
            Decl::FnSig(sig) => sig.name.clone(),
            Decl::Struct(s) => Some(s.name.path.to_string()),
            Decl::Trait(t) => Some(t.ty.name()),
            Decl::TypeAlias(_, _) | Decl::Impl(_) | Decl::Declare(_) => None,
        }
    }
}
