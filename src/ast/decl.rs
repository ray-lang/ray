use crate::span::Span;
use crate::strutils;
use crate::{ast, pathlib::FilePath};

#[derive(Clone, Debug)]
pub enum DeclKind {
    Extern(Box<Decl>),
    Name(ast::Name),
    Declare(ast::Assign),
    Fn(ast::FnSig),
    Struct(ast::Struct),
    Proto(ast::Proto),
    TypeAlias(ast::Name, ast::Type),
    Impl(ast::Impl),
}

#[derive(Clone, Debug)]
pub struct Decl {
    pub kind: DeclKind,
    pub span: Span,
    pub filepath: FilePath,
    pub id: ast::Id,
}

#[derive(Clone, Debug)]
pub struct Struct {
    pub name: ast::Name,
    pub ty_params: Option<ast::TypeParams>,
    pub fields: Option<Vec<ast::Name>>,
}

#[derive(Clone, Debug)]
pub struct Proto {
    pub name: ast::Name,
    pub ty_params: Option<ast::TypeParams>,
    pub methods: Vec<ast::FnSig>,
    pub base_proto_ty: Option<ast::Type>,
}

#[derive(Clone, Debug)]
pub struct Impl {
    pub ty_params: Option<ast::TypeParams>,
    pub funcs: Option<Vec<ast::Fn>>,
    pub externs: Option<Vec<Decl>>,
    pub consts: Option<Vec<ast::Expr>>,
    pub base_ty: ast::Type,
    pub proto_ty: Option<ast::Type>,
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
            DeclKind::Proto(ref p) => {
                let tp = if let Some(ref tp) = p.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                if p.methods.len() != 0 {
                    let methods = format!("{}\n", strutils::indent_lines_iter(&p.methods, 2));
                    write!(f, "(protocol {}{}\n{})", p.name, tp, methods)
                } else {
                    write!(f, "(protocol {}{}\n)", p.name, tp)
                }
            }
            DeclKind::Impl(ref im) => {
                let tp = if let Some(ref tp) = im.ty_params {
                    tp.to_string()
                } else {
                    "".to_string()
                };

                let ty = if let Some(ref p) = im.proto_ty {
                    format!("({}: {})", im.base_ty, p)
                } else {
                    im.base_ty.to_string()
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
                    write!(f, "(impl{} {}\n{}{}{})", tp, ty, externs, consts, funcs)
                } else {
                    write!(f, "(impl{} {})", tp, ty)
                }
            }
        }
    }
}
