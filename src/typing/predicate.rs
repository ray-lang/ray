use std::collections::HashSet;

use crate::{
    ast,
    errors::{RayError, RayErrorKind},
    pathlib::FilePath,
    span::Source,
    utils::join,
};

use super::{
    top::{
        state::TyVarFactory,
        traits::{HasFreeVars, Instantiate},
    },
    ty::{LiteralKind, Ty, TyVar},
    ApplySubst, Ctx, Subst,
};

pub trait PredicateEntails<Other = Self> {
    fn entails(&self, other: &Other, ctx: &Ctx) -> bool;
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyPredicate {
    Trait(Ty),
    Literal(Ty, LiteralKind),
}

impl std::fmt::Debug for TyPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyPredicate::Trait(p) => write!(f, "{:?}", p),
            TyPredicate::Literal(t, k) => write!(f, "{:?} is {:?}", t, k),
        }
    }
}

impl std::fmt::Display for TyPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyPredicate::Trait(p) => write!(f, "{}", p),
            TyPredicate::Literal(t, k) => write!(f, "{} is {}", t, k),
        }
    }
}

impl ApplySubst for TyPredicate {
    fn apply_subst(self, subst: &Subst) -> TyPredicate {
        match self {
            TyPredicate::Trait(p) => TyPredicate::Trait(p.apply_subst(subst)),
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.apply_subst(subst), k),
        }
    }
}

impl HasFreeVars for TyPredicate {
    fn free_vars(&self) -> HashSet<&TyVar> {
        let mut h = HashSet::new();
        match self {
            TyPredicate::Trait(p) => {
                h.extend(p.free_vars());
            }
            TyPredicate::Literal(t, _) => {
                h.extend(t.free_vars());
            }
        }

        h
    }
}

impl Instantiate for TyPredicate {
    fn instantiate(self, tf: &mut TyVarFactory) -> TyPredicate {
        match self {
            TyPredicate::Trait(p) => TyPredicate::Trait(p.instantiate(tf)),
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.instantiate(tf), k),
        }
    }
}

impl PredicateEntails<Vec<TyPredicate>> for Vec<TyPredicate> {
    fn entails(&self, q: &Vec<TyPredicate>, ctx: &Ctx) -> bool {
        q.iter().all(|q| self.entails(q, ctx))
    }
}

impl PredicateEntails<TyPredicate> for Vec<TyPredicate> {
    fn entails(&self, q: &TyPredicate, ctx: &Ctx) -> bool {
        match q {
            TyPredicate::Trait(trait_ty) => {
                let base_ty = trait_ty.get_ty_param_at(0);

                // look through all of the traits and find the traits that include
                // the trait type in `q` as a super trait, meaning find all of the
                // subtraits of the trait type
                let subtraits = ctx.get_subtraits(trait_ty);
                if subtraits.into_iter().any(|s| {
                    let s = s.clone().set_ty_params(vec![base_ty.clone()]);
                    let p = TyPredicate::Trait(s);
                    self.entails(&p, ctx)
                }) {
                    return true;
                }

                // find all of the impls of the trait in `q`
                if let Some(impls) = ctx.get_impls(trait_ty) {
                    impls
                        .iter()
                        .filter(|i| {
                            // unify the base types
                            let sub = match i.base_ty.mgu(base_ty) {
                                Ok(s) => s,
                                _ => return false,
                            };

                            let lhs = i.base_ty.clone().apply_subst(&sub);
                            let rhs = base_ty.clone().apply_subst(&sub);
                            lhs == rhs
                        })
                        .all(|i| {
                            // and then check that the predicates hold for the impl
                            self.entails(&i.predicates, ctx)
                        })
                } else {
                    false
                }
            }
            TyPredicate::Literal(t, k) => match k {
                LiteralKind::Int => t.is_int_ty(),
                LiteralKind::Float => t.is_float_ty(),
            },
        }
    }
}

impl TyPredicate {
    pub fn from_ast_ty(
        q: &ast::Type,
        scope: &ast::Path,
        filepath: &FilePath,
        ctx: &mut Ctx,
    ) -> Result<TyPredicate, RayError> {
        let (s, v) = match Ty::from_ast_ty(&q.kind, scope, ctx) {
            Ty::Projection(s, v) => (s, v),
            _ => {
                return Err(RayError {
                    msg: str!("qualifier must be a trait type"),
                    src: vec![Source {
                        span: Some(q.span.unwrap()),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                })
            }
        };

        if v.len() != 1 {
            return Err(RayError {
                msg: format!("traits must have one type argument, but found {}", v.len()),
                src: vec![Source {
                    span: Some(q.span.unwrap()),
                    filepath: filepath.clone(),
                }],
                kind: RayErrorKind::Type,
            });
        }

        let ty_arg = v[0].clone();
        let fqn = match ctx.lookup_fqn(&s) {
            Some(fqn) => fqn,
            _ => {
                return Err(RayError {
                    msg: format!("trait `{}` is not defined", s),
                    src: vec![Source {
                        span: Some(q.span.unwrap()),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                })
            }
        };

        let trait_ty = match ctx.get_trait_ty(&fqn) {
            Some(t) => t,
            _ => {
                return Err(RayError {
                    msg: format!("trait `{}` is not defined", s),
                    src: vec![Source {
                        span: Some(q.span.unwrap()),
                        filepath: filepath.clone(),
                    }],
                    kind: RayErrorKind::Type,
                })
            }
        };

        let trait_ty = trait_ty.ty.clone();
        let ty_param = variant!(Ty::Var(_), trait_ty.get_ty_param_at(0).clone()).unwrap();
        let sub = subst! { ty_param => ty_arg };
        let trait_ty = trait_ty.apply_subst(&sub);
        Ok(TyPredicate::Trait(trait_ty))
    }
}
