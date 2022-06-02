use crate::{
    errors::{RayError, RayErrorKind},
    span::Source,
    typing::subst::ApplySubst,
};

use super::{
    predicate::TyPredicate,
    ty::{Ty, TyVar},
    Subst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeErrorKind {
    Message(String),
    Assertion(String, Ty),
    Mismatch(Ty, Ty),
    Equality(Ty, Ty),
    InstanceOf(Ty, Ty),
    UnsolvableTyVar(TyVar),
    Predicate(TyPredicate),
    RecursiveUnification(Ty, Ty),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
    pub src: Vec<Source>,
}

impl From<TypeError> for RayError {
    fn from(err: TypeError) -> Self {
        RayError {
            msg: err.message(),
            src: err.src,
            kind: RayErrorKind::Type,
        }
    }
}

impl ApplySubst for TypeError {
    fn apply_subst(self, subst: &Subst) -> Self {
        todo!()
    }
}

impl TypeError {
    pub fn new(msg: String) -> Self {
        Self {
            kind: TypeErrorKind::Message(msg),
            src: vec![],
        }
    }

    pub fn assertion<Msg: Into<String>>(msg: Msg, ty: Ty) -> Self {
        Self {
            kind: TypeErrorKind::Assertion(msg.into(), ty),
            src: vec![],
        }
    }

    pub fn mismatch(a: Ty, b: Ty) -> Self {
        Self {
            kind: TypeErrorKind::Mismatch(a, b),
            src: vec![],
        }
    }

    pub fn equality(a: Ty, b: Ty) -> Self {
        Self {
            kind: TypeErrorKind::Equality(a, b),
            src: vec![],
        }
    }

    pub fn instance_of(a: Ty, b: Ty) -> Self {
        Self {
            kind: TypeErrorKind::InstanceOf(a, b),
            src: vec![],
        }
    }

    pub fn tyvar(v: TyVar) -> Self {
        Self {
            kind: TypeErrorKind::UnsolvableTyVar(v),
            src: vec![],
        }
    }

    pub fn predicate(pred: TyPredicate) -> Self {
        Self {
            kind: TypeErrorKind::Predicate(pred),
            src: vec![],
        }
    }

    pub fn recursive_unify(a: Ty, b: Ty) -> Self {
        Self {
            kind: TypeErrorKind::RecursiveUnification(a, b),
            src: vec![],
        }
    }

    pub fn message(&self) -> String {
        match &self.kind {
            TypeErrorKind::Message(msg) => msg.clone(),
            TypeErrorKind::Assertion(a, b) => {
                format!("expected {} type, but found {}", a, b)
            }
            TypeErrorKind::Mismatch(a, b) => {
                format!("type mismatch: `{}` and `{}`", a, b)
            }
            TypeErrorKind::Equality(a, b) => format!("types `{}` and `{}` are not equal", a, b),
            TypeErrorKind::InstanceOf(a, b) => {
                format!("type `{}` is not an instance of type `{}`", a, b)
            }
            TypeErrorKind::UnsolvableTyVar(v) => format!("type variable `{}` cannot be solved", v),
            TypeErrorKind::Predicate(pred) => format!("expression does not {}", pred.desc()),
            TypeErrorKind::RecursiveUnification(a, b) => {
                format!("recursive unification: {} and {}", a, b)
            }
        }
    }
}
