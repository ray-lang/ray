use crate::{
    ast::Path,
    span::{parsed::Parsed, Span},
    typing::ty::Ty,
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name {
    pub path: Path,
    pub ty: Option<Parsed<Ty>>,
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref t) = self.ty {
            write!(f, "{}: {}", self.path, t)
        } else {
            write!(f, "{}", self.path)
        }
    }
}

impl Name {
    pub fn new<P: Into<Path>>(path: P) -> Name {
        Name {
            path: path.into(),
            ty: None,
        }
    }

    pub fn typed<P: Into<Path>>(path: P, ty: Parsed<Ty>) -> Name {
        Name {
            path: path.into(),
            ty: Some(ty),
        }
    }
}
