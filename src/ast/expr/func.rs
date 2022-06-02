use crate::{
    ast::{Expr, Modifier, Name, Node, Path, TypeParams},
    span::{parsed::Parsed, Source, Span},
    typing::ty::Ty,
};

use super::Decl;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FnParam {
    Name(Name),
    DefaultValue(Box<Node<FnParam>>, Box<Node<Expr>>),
}

impl std::fmt::Display for FnParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnParam::Name(n) => write!(f, "{}", n),
            FnParam::DefaultValue(p, v) => write!(f, "{} = {}", p, v),
        }
    }
}

impl FnParam {
    pub fn name(&self) -> Option<&Path> {
        match self {
            FnParam::DefaultValue(p, _) => p.name(),
            FnParam::Name(n) => Some(&n.path),
        }
    }

    pub fn ty(&self) -> Option<&Ty> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty(),
            FnParam::Name(n) => n.ty.as_deref(),
        }
    }

    pub fn ty_mut(&mut self) -> Option<&mut Ty> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty_mut(),
            FnParam::Name(n) => n.ty.as_deref_mut(),
        }
    }

    pub fn set_ty(&mut self, ty: Ty) {
        match self {
            FnParam::DefaultValue(p, _) => p.set_ty(ty),
            FnParam::Name(n) => {
                n.ty = Some(Parsed::new(ty, Source::default()));
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncSig {
    pub path: Path,
    pub name: Option<String>,
    pub params: Vec<Node<FnParam>>,
    pub ty_params: Option<TypeParams>,
    pub ret_ty: Option<Parsed<Ty>>,
    pub ty: Option<Ty>,
    pub modifiers: Vec<Modifier>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub doc_comment: Option<String>,
    pub is_method: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Func {
    pub sig: FuncSig,
    pub body: Option<Box<Node<Expr>>>,
}

impl Func {
    pub fn new(path: Path, params: Vec<Node<FnParam>>, body: Node<Expr>) -> Self {
        Self {
            sig: FuncSig {
                path,
                name: None,
                params,
                ty_params: None,
                ret_ty: None,
                ty: None,
                modifiers: vec![],
                qualifiers: vec![],
                doc_comment: None,
                is_method: false,
                span: Span::new(),
            },
            body: Some(Box::new(body)),
        }
    }
}

impl std::fmt::Display for FuncSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ty_params = if let Some(ref ty_params) = self.ty_params {
            ty_params.to_string()
        } else {
            String::new()
        };
        let ret_ty = self
            .ret_ty
            .as_ref()
            .map_or_else(|| "".to_string(), |t| format!(" -> {}", t));
        write!(
            f,
            "{}{}({}){}",
            self.name
                .as_ref()
                .map_or_else(|| "__anon__".to_string(), |n| n.to_string()),
            ty_params,
            self.params
                .iter()
                .map(|p| p.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            ret_ty,
        )
    }
}

impl std::fmt::Display for Func {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let body = self.body.as_ref();
        write!(
            f,
            "(fn {}{}{})",
            self.sig,
            if body
                .map(|body| { !matches!(body.value, Expr::Block(_)) })
                .unwrap_or_default()
            {
                " => "
            } else {
                ""
            },
            body.map_or_else(|| str!(""), |b| b.to_string()),
        )
    }
}
