use crate::{
    ast::{Assign, Expr, FnSig, Name, Node, Type, TypeKind, TypeParams},
    strutils,
    utils::join,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Extern(Box<Node<Decl<Info>, Info>>),
    Name(Name),
    Declare(Assign<Info>),
    Fn(FnSig<Info>),
    Struct(Struct),
    Trait(Trait<Info>),
    TypeAlias(Name, Type),
    Impl(Impl<Info>),
}

impl<Info> PartialOrd for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq + Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let i: usize = self.into();
        let j: usize = other.into();
        i.partial_cmp(&j)
    }
}

impl<Info> Ord for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq + Ord,
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
            Decl::Fn(_) => 4,
            Decl::Impl(_) => 5,
            Decl::Declare(_) => 6,
            Decl::Name(_) => 7,
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
    pub ty: Type,
    pub funcs: Vec<FnSig<Info>>,
    pub super_trait: Option<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Impl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub ty: Type,
    pub qualifiers: Vec<Type>,
    pub externs: Option<Vec<Node<Decl<Info>, Info>>>,
    pub funcs: Option<Vec<Node<Expr<Info>, Info>>>,
    pub consts: Option<Vec<Node<Expr<Info>, Info>>>,
}

impl<Info> std::fmt::Display for Decl<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Decl::Extern(ref ext) => write!(f, "(extern {})", ext),
            Decl::Name(ref n) => write!(f, "(declare {})", n),
            Decl::Declare(ref a) => write!(f, "(declare {})", a),
            Decl::TypeAlias(ref n, ref ty) => write!(f, "(type {} = {})", n, ty),
            Decl::Fn(ref sig) => write!(f, "(fn {})", sig),
            Decl::Struct(ref st) => {
                let tp = if let Some(ref tp) = st.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                if let Some(ref fields) = st.fields {
                    let fields = format!("{}\n", strutils::indent_lines_iter(fields, 2));
                    write!(f, "(struct {}{} {{\n{}}})", st.name, tp, fields)
                } else {
                    write!(f, "(struct {}{})", st.name, tp)
                }
            }
            Decl::Trait(ref tr) => {
                if tr.funcs.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&tr.funcs, 2));
                    write!(f, "(trait {}\n{})", tr.ty, methods)
                } else {
                    write!(f, "(trait {}\n)", tr.ty)
                }
            }
            Decl::Impl(ref im) => {
                let qualifiers = if im.qualifiers.len() != 0 {
                    format!("where {}", join(&im.qualifiers, ", "))
                } else {
                    str!("")
                };

                let funcs = if let Some(ref funcs) = im.funcs {
                    let s = format!("{}", strutils::indent_lines_iter(funcs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let externs = if let Some(ref externs) = im.externs {
                    let s = format!("{}", strutils::indent_lines_iter(externs, 2));
                    if s.len() == 0 {
                        "".to_string()
                    } else {
                        format!("{}\n", s)
                    }
                } else {
                    "".to_string()
                };

                let consts = if let Some(ref consts) = im.consts {
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
            Decl::Name(n) => Some(n.name.clone()),
            Decl::Fn(f) => f.name.clone(),
            Decl::Struct(s) => Some(s.name.name.clone()),
            Decl::Trait(t) => match &t.ty.kind {
                TypeKind::Basic { name, .. } => Some(name.clone()),
                _ => None,
            },
            Decl::TypeAlias(_, _) | Decl::Impl(_) | Decl::Declare(_) => None,
        }
    }
}
