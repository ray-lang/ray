use super::{traits::HasType, ty::Ty, ApplySubst};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeInfo {
    ty: Ty,
}

impl HasType for TypeInfo {
    fn ty(&self) -> Ty {
        self.ty.clone()
    }
}

impl ApplySubst for TypeInfo {
    fn apply_subst(self, subst: &super::Subst) -> Self {
        TypeInfo {
            ty: self.ty.apply_subst(subst),
        }
    }
}

impl TypeInfo {
    pub fn new(ty: Ty) -> TypeInfo {
        TypeInfo { ty }
    }
}
