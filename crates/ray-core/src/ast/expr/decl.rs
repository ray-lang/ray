use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use itertools::Itertools;

use crate::{
    ast::{Assign, Func, FuncSig, Name, Node, Path, TypeParams},
    span::parsed::Parsed,
    strutils,
    typing::ty::{NominalKind, Ty, TyScheme},
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

    pub fn decl_node(&self) -> &Node<Decl> {
        &self.decl
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
    Func(Func),
    FnSig(FuncSig),
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
            Decl::Func(_) | Decl::FnSig(_) => 4,
            Decl::Impl(_) => 5,
            Decl::Declare(_) => 6,
            Decl::Mutable(_) | Decl::Name(_) => 7,
        }
    }
}

impl Decl {
    pub fn desc(&self) -> String {
        match self {
            Decl::Extern(e) => format!("extern {}", e.decl().desc()),
            Decl::Mutable(_) => todo!("mutable variable"),
            Decl::Name(_) => todo!("variable"),
            Decl::Declare(_) => todo!("variable"),
            Decl::Func(_) => str!("function"),
            Decl::FnSig(_) => str!("function signature"),
            Decl::Struct(st) => st.kind.to_string(),
            Decl::Trait(_) => str!("trait"),
            Decl::TypeAlias(_, _) => str!("type alias"),
            Decl::Impl(_) => str!("impl"),
        }
    }

    pub fn is_typed(&self) -> bool {
        match self {
            Decl::Extern(_) | Decl::Struct(_) | Decl::Trait(_) | Decl::TypeAlias(_, _) => true,
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => f.sig.ty.is_some(),
            Decl::FnSig(sig) => sig.ty.is_some(),
            Decl::Impl(_) => false, // not entirely true, but we don't care here
        }
    }

    pub fn get_ty(&self) -> Option<&TyScheme> {
        match self {
            Decl::Extern(_)
            | Decl::Impl(_)
            | Decl::Struct(_)
            | Decl::Trait(_)
            | Decl::TypeAlias(_, _) => todo!(),
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => f.sig.ty.as_ref(),
            Decl::FnSig(sig) => sig.ty.as_ref(),
        }
    }

    pub fn get_defs(&self) -> HashMap<&Path, Option<&TyScheme>> {
        let mut defs = HashMap::new();
        match self {
            Decl::Extern(ex) => defs.extend(ex.decl().get_defs()),
            Decl::Mutable(_) => todo!(),
            Decl::Name(_) => todo!(),
            Decl::Declare(_) => todo!(),
            Decl::Func(f) => {
                defs.insert(&f.sig.path, f.sig.ty.as_ref());
            }
            Decl::FnSig(sig) => {
                defs.insert(&sig.path, sig.ty.as_ref());
            }
            Decl::Struct(_) => todo!(),
            Decl::Trait(tr) => {
                for func in tr.fields.iter() {
                    let func = variant!(func.deref(), if Decl::FnSig(func));
                    defs.insert(&func.path, func.ty.as_ref());
                }
            }
            Decl::TypeAlias(_, _) => todo!(),
            Decl::Impl(im) => {
                if let Some(externs) = &im.externs {
                    defs.extend(externs.iter().map(|d| d.get_defs()).concat());
                }

                if let Some(funcs) = &im.funcs {
                    defs.extend(funcs.iter().map(|f| (&f.sig.path.value, f.sig.ty.as_ref())));
                }

                if let Some(consts) = &im.consts {
                    defs.extend(
                        consts
                            .iter()
                            .flat_map(|d| d.lhs.path().map(|path| (path, None))),
                    );
                }
            }
        }
        defs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Struct {
    pub kind: NominalKind,
    pub path: Node<Path>,
    pub ty_params: Option<TypeParams>,
    pub fields: Option<Vec<Node<Name>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trait {
    pub path: Node<Path>,
    pub ty: Parsed<Ty>,
    pub fields: Vec<Node<Decl>>,
    pub super_trait: Option<Parsed<Ty>>,
    pub directives: Vec<Parsed<TraitDirective>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraitDirectiveKind {
    Default,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraitDirective {
    pub kind: TraitDirectiveKind,
    pub args: Vec<Parsed<Ty>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Impl {
    pub ty: Parsed<Ty>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub externs: Option<Vec<Node<Decl>>>,
    pub funcs: Option<Vec<Node<Func>>>,
    pub consts: Option<Vec<Node<Assign>>>,
    pub is_object: bool,
}

impl std::fmt::Display for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Extern(ext) => write!(f, "(extern {})", ext),
            Decl::Mutable(n) => write!(f, "(mut {})", n),
            Decl::Name(n) => write!(f, "(declare {})", n),
            Decl::Declare(a) => write!(f, "(declare {})", a),
            Decl::TypeAlias(n, ty) => write!(f, "(type {} = {})", n, ty),
            Decl::Func(func) => write!(f, "{}", func),
            Decl::FnSig(sig) => write!(f, "(fn {})", sig),
            Decl::Struct(st) => {
                let tp = if let Some(tp) = &st.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                if let Some(fields) = &st.fields {
                    let fields = format!("{}\n", strutils::indent_lines_iter(fields, 2));
                    write!(f, "(struct {}{} {{\n{}}})", st.path, tp, fields)
                } else {
                    write!(f, "(struct {}{})", st.path, tp)
                }
            }
            Decl::Trait(tr) => {
                if tr.fields.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&tr.fields, 2));
                    write!(f, "(trait {}\n{})", tr.ty, methods)
                } else {
                    write!(f, "(trait {}\n)", tr.ty)
                }
            }
            Decl::Impl(im) => {
                let qualifiers = if im.qualifiers.len() != 0 {
                    format!("where {}", join(&im.qualifiers, " + "))
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
            Decl::Func(f) => f.sig.path.name(),
            Decl::FnSig(sig) => sig.path.name(),
            Decl::Struct(s) => s.path.name(),
            Decl::Trait(t) => Some(t.ty.name()),
            Decl::TypeAlias(_, _) | Decl::Impl(_) | Decl::Declare(_) => None,
        }
    }
}
