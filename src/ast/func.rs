use crate::ast::{Decorator, Expr, Modifier, Name, Type, TypeParams};
use crate::span::Span;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnParam {
    Name(Name),
    Type(Type),
    DefaultValue(Box<FnParam>, Box<Expr>),
}

impl std::fmt::Display for FnParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnParam::Name(n) => write!(f, "{}", n),
            FnParam::Type(t) => write!(f, "{}", t),
            FnParam::DefaultValue(p, v) => write!(f, "{} = {}", p, v),
        }
    }
}

impl FnParam {
    pub fn name(&self) -> Option<&String> {
        match self {
            FnParam::DefaultValue(p, _) => p.name(),
            FnParam::Name(n) => Some(&n.name),
            FnParam::Type(_) => None,
        }
    }

    pub fn ty(&self) -> Option<&Type> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty(),
            FnParam::Name(n) => n.ty.as_ref(),
            FnParam::Type(t) => Some(t),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            FnParam::DefaultValue(p, e) => p.span().extend_to(&e.src.span.unwrap()),
            FnParam::Name(n) => n.span,
            FnParam::Type(t) => t.span.unwrap(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnSig {
    pub name: Option<String>,
    pub params: Vec<FnParam>,
    pub ty_params: Option<TypeParams>,
    pub ret_ty: Option<Type>,
    pub ty: Option<Type>,
    pub modifiers: Vec<Modifier>,
    pub qualifiers: Vec<Type>,
    pub doc_comment: Option<String>,
    pub decorators: Option<Vec<Decorator>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fn {
    pub sig: FnSig,
    pub body: Option<Box<Expr>>,
    pub span: Span,
}

impl std::fmt::Display for FnSig {
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
impl std::fmt::Display for Fn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(fn {} {})",
            self.sig,
            self.body
                .as_ref()
                .map_or_else(|| "".to_string(), |b| b.to_string()),
        )
    }
}
