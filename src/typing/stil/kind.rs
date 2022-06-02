use crate::typing::ty::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind<'a> {
    Star,
    Fn(&'a Kind<'a>, &'a Kind<'a>),
}

pub trait HasKind {
    fn kind(&self) -> Kind;
}

impl HasKind for Ty {
    fn kind(&self) -> Kind {
        match self {
            Ty::Never => todo!(),
            Ty::Any => todo!(),
            Ty::Var(_) => todo!(),
            Ty::Tuple(_) => todo!(),
            Ty::Ptr(_) => todo!(),
            Ty::Union(_) => todo!(),
            Ty::Array(_, _) => todo!(),
            Ty::Func(_, _) => todo!(),
            Ty::Projection(_, _) => todo!(),
            Ty::Qualified(_, _) => todo!(),
            Ty::All(_, _) => todo!(),
        }
    }
}
