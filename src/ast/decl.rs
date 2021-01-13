use crate::strutils;
use crate::{ast, span::Span};
use crate::{span::Source, utils::join};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Extern(Box<Decl>),
    Name(ast::Name),
    Declare(ast::Assign),
    Fn(ast::FnSig),
    Struct(ast::Struct),
    Trait(ast::Trait),
    TypeAlias(ast::Name, ast::Type),
    Impl(ast::Impl),
}

impl PartialOrd for DeclKind {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let i: usize = self.into();
        let j: usize = other.into();
        i.partial_cmp(&j)
    }
}

impl Ord for DeclKind {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let i: usize = self.into();
        let j: usize = other.into();
        i.cmp(&j)
    }
}

impl Into<usize> for &DeclKind {
    fn into(self) -> usize {
        match self {
            DeclKind::Trait(_) => 0,
            DeclKind::Struct(_) => 1,
            DeclKind::TypeAlias(_, _) => 2,
            DeclKind::Extern(_) => 3,
            DeclKind::Fn(_) => 4,
            DeclKind::Impl(_) => 5,
            DeclKind::Declare(_) => 6,
            DeclKind::Name(_) => 7,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub kind: DeclKind,
    pub src: Source,
    pub id: ast::Id,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Struct {
    pub name: ast::Name,
    pub ty_params: Option<ast::TypeParams>,
    pub fields: Option<Vec<ast::Name>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trait {
    pub ty: ast::Type,
    pub funcs: Vec<ast::FnSig>,
    pub super_trait: Option<ast::Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Impl {
    pub ty: ast::Type,
    pub qualifiers: Vec<ast::Type>,
    pub externs: Option<Vec<Decl>>,
    pub funcs: Option<Vec<ast::Expr>>,
    pub consts: Option<Vec<ast::Expr>>,
}

impl std::fmt::Display for Decl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            DeclKind::Extern(ref ext) => write!(f, "(extern {})", ext),
            DeclKind::Name(ref n) => write!(f, "(declare {})", n),
            DeclKind::Declare(ref a) => write!(f, "(declare {})", a),
            DeclKind::TypeAlias(ref n, ref ty) => write!(f, "(type {} = {})", n, ty),
            DeclKind::Fn(ref sig) => write!(f, "(fn {})", sig),
            DeclKind::Struct(ref st) => {
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
            DeclKind::Trait(ref tr) => {
                if tr.funcs.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&tr.funcs, 2));
                    write!(f, "(trait {}\n{})", tr.ty, methods)
                } else {
                    write!(f, "(trait {}\n)", tr.ty)
                }
            }
            DeclKind::Impl(ref im) => {
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

impl Decl {
    pub fn get_name(&self) -> Option<String> {
        match &self.kind {
            DeclKind::Extern(e) => e.get_name(),
            DeclKind::Name(n) => Some(n.name.clone()),
            DeclKind::Fn(f) => f.name.clone(),
            DeclKind::Struct(s) => Some(s.name.name.clone()),
            DeclKind::Trait(t) => match &t.ty.kind {
                ast::TypeKind::Basic { name, .. } => Some(name.clone()),
                _ => None,
            },
            DeclKind::TypeAlias(_, _) | DeclKind::Impl(_) | DeclKind::Declare(_) => None,
        }
    }
}
