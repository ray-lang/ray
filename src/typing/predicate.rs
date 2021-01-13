use std::collections::{HashMap, HashSet};

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
        traits::{FreezeVars, HasFreeVars},
    },
    ty::{LiteralKind, Ty, TyVar},
    ApplySubst, Ctx, Subst,
};

pub trait PredicateEntails<Other = Self> {
    fn entails(&self, other: &Other, ctx: &Ctx) -> bool;
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyPredicate {
    Trait(Ty, Ty),
    Literal(Ty, LiteralKind),
}

impl std::fmt::Display for TyPredicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TyPredicate::Trait(t, p) => write!(f, "{} <: {}", t, p),
            TyPredicate::Literal(t, k) => write!(f, "{} is {}", t, k),
        }
    }
}

impl ApplySubst for TyPredicate {
    fn apply_subst(self, subst: &Subst) -> TyPredicate {
        match self {
            TyPredicate::Trait(t, p) => {
                TyPredicate::Trait(t.apply_subst(subst), p.apply_subst(subst))
            }
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.apply_subst(subst), k),
        }
    }
}

impl HasFreeVars for TyPredicate {
    fn free_vars(&self) -> HashSet<&TyVar> {
        let mut h = HashSet::new();
        match self {
            TyPredicate::Trait(t, p) => {
                h.extend(t.free_vars());
                h.extend(p.free_vars());
            }
            TyPredicate::Literal(t, _) => {
                h.extend(t.free_vars());
            }
        }

        h
    }
}

// impl PredicateEntails<TyPredicate> for Ctx {
//     fn entails(&self, p: &TyPredicate, _: &Ctx) -> bool {
//         match p {
//             TyPredicate::Trait(base_ty, trait_ty) => {
//                 // ensure that `base_ty` implements `trait_ty`
//                 self.implements(base_ty, trait_ty, &vec![])
//             }
//             TyPredicate::Literal(_, _) => todo!(),
//         }
//     }
// }

impl PredicateEntails<Vec<TyPredicate>> for Vec<TyPredicate> {
    fn entails(&self, q: &Vec<TyPredicate>, ctx: &Ctx) -> bool {
        println!("{{{}}} entails {{{}}}", join(self, ", "), join(q, ", "));

        q.iter().all(|q| self.entails(q, ctx))
    }
}

impl PredicateEntails<TyPredicate> for Vec<TyPredicate> {
    fn entails(&self, q: &TyPredicate, ctx: &Ctx) -> bool {
        match q {
            TyPredicate::Trait(base_ty, trait_ty) => {
                println!("base type: {}", base_ty);
                println!("trait type: {}", trait_ty);

                // look through all of the traits and find the traits that include
                // the trait type in `q` as a super trait, meaning find all of the
                // subtraits of the trait type
                let subtraits = ctx.get_subtraits(trait_ty);
                if subtraits.into_iter().any(|s| {
                    let s = s.clone().set_ty_params(vec![base_ty.clone()]);
                    println!("subtrait: {}", &s);
                    let p = TyPredicate::Trait(base_ty.clone(), s);
                    self.entails(&p, ctx)
                }) {
                    return true;
                }

                // find all of the impls of the trait in `q`
                if let Some(impls) = ctx.get_impls(trait_ty) {
                    impls
                        .iter()
                        .filter(|i| {
                            println!("impl base type: {}", i.base_ty);

                            // unify the base types
                            let sub = match i.base_ty.mgu(base_ty) {
                                Ok(s) => s,
                                _ => return false,
                            };

                            println!("sub: {:?}", sub);
                            let lhs = i.base_ty.clone().apply_subst(&sub);
                            let rhs = base_ty.clone().apply_subst(&sub);
                            println!("lhs = {}", lhs);
                            println!("rhs = {}", rhs);
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

impl FreezeVars for TyPredicate {
    fn freeze_tyvars(self) -> TyPredicate {
        match self {
            TyPredicate::Trait(s, t) => TyPredicate::Trait(s.freeze_tyvars(), t.freeze_tyvars()),
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.freeze_tyvars(), k),
        }
    }

    fn unfreeze_tyvars(self) -> Self {
        match self {
            TyPredicate::Trait(s, t) => {
                TyPredicate::Trait(s.unfreeze_tyvars(), t.unfreeze_tyvars())
            }
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.unfreeze_tyvars(), k),
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
        let sub = subst! { ty_param => ty_arg.clone() };
        let trait_ty = trait_ty.apply_subst(&sub);
        Ok(TyPredicate::Trait(ty_arg, trait_ty))
    }

    pub fn instantiate(self, tf: &mut TyVarFactory) -> TyPredicate {
        match self {
            TyPredicate::Trait(s, t) => TyPredicate::Trait(s.instantiate(tf), t.instantiate(tf)),
            TyPredicate::Literal(t, k) => TyPredicate::Literal(t.instantiate(tf), k),
        }
    }

    pub fn match_predicate(&self, q: &TyPredicate) -> Option<Subst> {
        let (s, t) = match (self, q) {
            (TyPredicate::Trait(s, t), TyPredicate::Trait(u, v)) if t == v => (s, u),
            (TyPredicate::Literal(s, k1), TyPredicate::Literal(t, k2)) if k1 == k2 => (s, t),
            _ => return None,
        };

        let sub = match s.clone().freeze_tyvars().mgu(&t) {
            Ok(sub) => sub,
            _ => return None,
        };

        Some(
            sub.into_iter()
                .map(|(x, y)| (x, y.unfreeze_tyvars()))
                .collect::<Subst>(),
        )
    }
}
