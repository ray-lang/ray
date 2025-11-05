use crate::typing::{predicate::TyPredicate, ty::TyVar};

pub struct Ambiguity {
    ty_var: TyVar,
    preds: Vec<TyPredicate>,
}

impl Ambiguity {
    pub fn new(ty_var: TyVar, preds: Vec<TyPredicate>) -> Ambiguity {
        Ambiguity { ty_var, preds }
    }

    pub fn ty_var(&self) -> &TyVar {
        &self.ty_var
    }

    pub fn preds(&self) -> &Vec<TyPredicate> {
        &self.preds
    }
}
