use crate::top::{Predicate, interface::basic::ErrorLabel};

use ray_shared::span::Source;

use crate::{
    info::{Info, TypeSystemInfo},
    ty::{Ty, TyVar},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeErrorKind {
    Message(String),
    Assertion(String, Ty),
    Mismatch(Ty, Ty),
    MismatchImpl(String, String, Ty, Ty),
    Equality(Ty, Ty),
    InstanceOf(Ty, Ty),
    UnsolvableTyVar(TyVar),
    Predicate(Predicate<Ty, TyVar>),
    RecursiveUnification(Ty, Ty),
    WithInfo(ErrorLabel, Vec<Info>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
    pub src: Vec<Source>,
}

impl TypeError {
    pub fn new(msg: String) -> Self {
        Self {
            kind: TypeErrorKind::Message(msg),
            src: vec![],
        }
    }

    pub fn from_info(label: ErrorLabel, info: TypeSystemInfo) -> Self {
        Self {
            kind: TypeErrorKind::WithInfo(label, info.info),
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

    pub fn unsolved_predicate(&self) -> Option<(&Predicate<Ty, TyVar>, &TypeSystemInfo)> {
        let TypeErrorKind::WithInfo(_, info) = &self.kind else {
            return None;
        };

        info.iter().find_map(|info| {
            let Info::UnsolvedPredicate(p, i) = info else {
                return None;
            };

            Some((p, i.as_ref()))
        })
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
            TypeErrorKind::MismatchImpl(kind, name, trait_ty, impl_ty) => {
                // method `add_check` has an incompatible type for trait
                // expected signature `fn(&mut _, &_, bool)`
                //    found signature `fn(&mut _, &_, u32)`
                format!(
                    "{} `{}` has an incompatible type for trait\nexpected signature `{}`\n   found signature `{}`",
                    kind, name, trait_ty, impl_ty
                )
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
            TypeErrorKind::WithInfo(label, info) => {
                let mut msg = String::new();
                let mut first = true;
                let mut add_line = |msg: &mut String, str: &str| {
                    if str.is_empty() {
                        return;
                    }

                    if !first {
                        msg.push_str("\n");
                    }

                    first = false;
                    msg.push_str(&str);
                };

                match label {
                    ErrorLabel::MissingPredicate => {
                        // the unsolved predicate info
                        let mut found = vec![];
                        let pred_info = info.iter().enumerate().find_map(|(idx, info)| {
                            let Info::MissingPredicate(Predicate::Class(name, ty, params, _)) =
                                info
                            else {
                                return None;
                            };

                            Some((idx, (name, ty, params)))
                        });

                        let scheme_info = info.iter().enumerate().find_map(|(idx, info)| {
                            let Info::SkolemizedTypeScheme(_, scheme) = info else {
                                return None;
                            };

                            Some((idx, scheme))
                        });

                        if let (Some((pred_idx, (name, ty, params))), Some((scheme_idx, scheme))) =
                            (pred_info, scheme_info)
                        {
                            let suffix = if !params.is_empty() {
                                format!(
                                    " with parameters [{}]",
                                    params
                                        .iter()
                                        .map(|p| format!("`{}`", p))
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                )
                            } else {
                                "".to_string()
                            };

                            add_line(
                                &mut msg,
                                &format!(
                                    "type `{}` in this signature\n  {}\ndoes not implement trait `{}`{}",
                                    ty, scheme, name, suffix,
                                ),
                            );

                            found.push(pred_idx);
                            found.push(scheme_idx);
                        }

                        // iterate through the rest
                        for (idx, i) in info.iter().enumerate() {
                            if found.contains(&idx) {
                                continue;
                            }

                            add_line(&mut msg, &i.to_string());
                        }
                    }
                    ErrorLabel::AmbiguousPredicate
                    | ErrorLabel::DisjointPredicates
                    | ErrorLabel::UnsolvedPredicate
                    | ErrorLabel::SkolemVersusConstant
                    | ErrorLabel::SkolemVersusSkolem
                    | ErrorLabel::EscapingSkolem
                    | ErrorLabel::RigidTypeVariable
                    | ErrorLabel::Unification => {
                        for i in info.iter() {
                            let str = i.to_string();
                            add_line(&mut msg, &str);
                        }
                    }
                }
                msg
            }
        }
    }
}
