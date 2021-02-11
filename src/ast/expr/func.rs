use crate::{
    ast::{Decorator, Expr, HasSource, Modifier, Name, Node, Path, TypeParams},
    span::{parsed::Parsed, Span},
    typing::ty::Ty,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FnParam<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Name(Name),
    Type(Parsed<Ty>),
    DefaultValue(Box<FnParam<Info>>, Box<Node<Expr<Info>, Info>>),
}

impl<Info> std::fmt::Display for FnParam<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnParam::Name(n) => write!(f, "{}", n),
            FnParam::Type(t) => write!(f, "{}", t),
            FnParam::DefaultValue(p, v) => write!(f, "{} = {}", p, v),
        }
    }
}

impl<Info> FnParam<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq + HasSource,
{
    pub fn span(&self) -> Span {
        match self {
            FnParam::DefaultValue(p, e) => p.span().extend_to(&e.info.src().span.unwrap()),
            FnParam::Name(n) => n.span,
            FnParam::Type(t) => *t.span().unwrap(),
        }
    }
}

impl<Info> FnParam<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub fn name(&self) -> Option<&String> {
        match self {
            FnParam::DefaultValue(p, _) => p.name(),
            FnParam::Name(n) => Some(&n.name),
            FnParam::Type(_) => None,
        }
    }

    pub fn ty(&self) -> Option<&Ty> {
        match self {
            FnParam::DefaultValue(p, _) => p.ty(),
            FnParam::Name(n) => n.ty.as_deref(),
            FnParam::Type(t) => Some(t),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnSig<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub path: Path,
    pub name: Option<String>,
    pub params: Vec<FnParam<Info>>,
    pub ty_params: Option<TypeParams>,
    pub ret_ty: Option<Parsed<Ty>>,
    pub ty: Option<Parsed<Ty>>,
    pub modifiers: Vec<Modifier>,
    pub qualifiers: Vec<Parsed<Ty>>,
    pub doc_comment: Option<String>,
    pub decorators: Option<Vec<Decorator>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fn<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub sig: FnSig<Info>,
    pub body: Option<Box<Node<Expr<Info>, Info>>>,
    pub span: Span,
}

impl<Info> std::fmt::Display for FnSig<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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

impl<Info> std::fmt::Display for Fn<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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
