use crate::{
    span::{parsed::Parsed, Span},
    typing::ty::Ty,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub name: String,
    pub ty: Option<Parsed<Ty>>,
    pub span: Span,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref t) = self.ty {
            write!(f, "{}: {}", self.name, t)
        } else {
            write!(f, "{}", self.name)
        }
    }
}
