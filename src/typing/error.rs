use top::Predicate;

use crate::{
    errors::{RayError, RayErrorKind},
    span::Source,
    // typing::subst::ApplySubst,
};

use super::{
    info::{Info, TypeSystemInfo},
    // predicate::TyPredicate,
    ty::{Ty, TyVar},
    // Subst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeErrorKind {
    Message(String),
    Assertion(String, Ty),
    Mismatch(Ty, Ty),
    Equality(Ty, Ty),
    InstanceOf(Ty, Ty),
    UnsolvableTyVar(TyVar),
    Predicate(Predicate<Ty, TyVar>),
    RecursiveUnification(Ty, Ty),
    WithInfo(Vec<Info>),
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

impl TypeError {
    pub fn new(msg: String) -> Self {
        Self {
            kind: TypeErrorKind::Message(msg),
            src: vec![],
        }
    }

    pub fn from_info(info: TypeSystemInfo) -> Self {
        Self {
            kind: TypeErrorKind::WithInfo(info.info),
            src: info.source,
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

    pub fn predicate(pred: Predicate<Ty, TyVar>) -> Self {
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
            TypeErrorKind::Message(_) => todo!(),
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
            TypeErrorKind::Predicate(pred) => {
                format!("expression does not implement {}", pred)
            }
            TypeErrorKind::RecursiveUnification(a, b) => {
                format!("recursive unification: {} and {}", a, b)
            }
            TypeErrorKind::WithInfo(info) => {
                let mut msg = String::new();
                for (x, i) in info.iter().enumerate() {
                    msg.push_str(&i.to_string());
                    if x < info.len() - 1 {
                        msg.push_str("\n");
                    }
                }
                msg
            }
        }
    }
}
