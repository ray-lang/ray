use crate::{
    ast::{Assign, Expr, Fn, FnSig, Name, Node, TypeParams},
    span::parsed::Parsed,
    strutils,
    typing::ty::Ty,
    utils::join,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Extern(Box<Node<Decl<Info>, Info>>),
    Mutable(Name),
    Name(Name),
    Declare(Assign<Info>),
    Fn(Fn<Info>),
    FnSig(FnSig<Info>),
    Struct(Struct),
    Trait(Trait<Info>),
    TypeAlias(Name, Parsed<Ty>),
    Impl(Impl<Info>),
}

impl<Info> PartialOrd for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let i: usize = self.into();
        let j: usize = other.into();
        i.partial_cmp(&j)
    }
}

impl<Info> Ord for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let i: usize = self.into();
        let j: usize = other.into();
        i.cmp(&j)
    }
}

impl<Info> Into<usize> for &Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Struct {
    pub name: Name,
    pub ty_params: Option<TypeParams>,
    pub fields: Option<Vec<Name>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trait<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub ty: Parsed<Ty>,
    pub funcs: Vec<FnSig<Info>>,
    pub super_trait: Option<Parsed<Ty>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Impl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub ty: Parsed<Ty>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub externs: Option<Vec<Node<Decl<Info>, Info>>>,
    pub funcs: Option<Vec<Node<Decl<Info>, Info>>>,
    pub consts: Option<Vec<Node<Expr<Info>, Info>>>,
}

impl<Info> std::fmt::Display for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

impl<Info> Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn get_name(&self) -> Option<String> {
        match &self {
            Decl::Extern(e) => e.get_name(),
            Decl::Mutable(n) | Decl::Name(n) => Some(n.name.clone()),
            Decl::Fn(f) => f.sig.name.clone(),
            Decl::FnSig(sig) => sig.name.clone(),
            Decl::Struct(s) => Some(s.name.name.clone()),
            Decl::Trait(t) => Some(t.ty.name()),
            Decl::TypeAlias(_, _) | Decl::Impl(_) | Decl::Declare(_) => None,
        }
    }
}
