use super::{traits::HasType, ty::Ty, ApplySubst, Subst};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeInfo {
    original_ty: Ty,
    ty: Ty,
}

impl HasType for TypeInfo {
    fn ty(&self) -> Ty {
        self.ty.clone()
    }
}

impl ApplySubst for TypeInfo {
    fn apply_subst(self, subst: &Subst) -> Self {
        TypeInfo {
            original_ty: self.original_ty,
            ty: self.ty.apply_subst(subst),
        }
    }
}

impl TypeInfo {
    pub fn new(ty: Ty) -> TypeInfo {
        TypeInfo {
            original_ty: ty.clone(),
            ty,
        }
    }

    pub fn original_ty(&self) -> &Ty {
        &self.original_ty
    }
}
