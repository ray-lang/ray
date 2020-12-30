use crate::ast::{Decorator, Expr, Modifier, Name, Type, TypeParams};
use crate::span::Span;

#[derive(Clone, Debug)]
pub struct FnSig {
    pub name: Option<String>,
    pub params: Vec<Name>,
    pub ty_params: Option<TypeParams>,
    pub ret_ty: Option<Type>,
    pub ty: Option<Type>,
    pub modifiers: Vec<Modifier>,
    pub doc_comment: Option<String>,
    pub decorators: Option<Vec<Decorator>>,
}

#[derive(Clone, Debug)]
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
