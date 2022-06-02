use std::{collections::{HashMap, HashSet}, result};

use crate::{context::TypeContext, variance::Variance};

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Top,
    Bot,
    Var(TVar),
    Union(Vec<Type>),
    All(TAll),
    Func(TFunc),
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Top => write!(f, "Top"),
            Type::Bot => write!(f, "Bot"),
            Type::Var(v) => write!(f, "{}", v),
            Type::Union(tys) => write!(
                f,
                "{}",
                tys.iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(" | ")
            ),
            Type::All(t) => write!(f, "{}", t),
            Type::Func(t) => write!(f, "{}", t),
        }
    }
}

impl Type {
    pub fn free_vars(&self) -> HashSet<&TVar> {
        match self {
            Type::Top | Type::Bot => HashSet::new(),
            Type::Var(t) => {
                let mut s = HashSet::new();
                s.insert(t);
                s
            }
            Type::Union(tys) => tys.iter().flat_map(|t| t.free_vars()).collect(),
            Type::Func(f) => f
                .params
                .iter()
                .chain(std::iter::once(f.ret_ty.as_ref()))
                .flat_map(|t| t.free_vars())
                .collect(),
            Type::All(t) => {
                let mut s = t.ty.free_vars();
                for (v, _) in t.tyvars.iter() {
                    s.remove(v);
                }
                s
            }
        }
    }

    pub fn elim_up(&self, vars: &HashSet<TVar>, tcx: &TypeContext) -> Type {
        println!("⇑ {}", self);
        match self {
            Type::Top => Type::Top,
            Type::Bot => Type::Bot,
            Type::Var(v) => {
                if vars.contains(v) {
                    if let Some(bounds) = tcx
                        .get_bounds(v)
                        .map(|bounds| bounds.iter().map(|t| t.elim_up(vars, tcx)).collect())
                    {
                        return Type::Union(bounds);
                    }
                }
                Type::Var(v.clone())
            }
            Type::Union(_) => todo!(),
            Type::Func(f) => {
                let params = f.params.iter().map(|p| p.elim_down(vars, tcx)).collect();
                let ret_ty = f.ret_ty.elim_up(vars, tcx);
                Type::Func(TFunc {
                    params,
                    ret_ty: Box::new(ret_ty),
                })
            }
            Type::All(t) => {
                if t.tyvars.iter().all(|(v, bounds)| {
                    bounds
                        .as_ref()
                        .map(|tys| {
                            tys.iter().all(|t| {
                                if let Type::Var(v) = t {
                                    !vars.contains(v)
                                } else {
                                    true
                                }
                            })
                        })
                        .unwrap_or(true)
                }) {
                    return Type::All(TAll {
                        tyvars: t.tyvars.clone(),
                        ty: Box::new(t.ty.elim_up(vars, tcx)),
                    });
                }
                Type::Top
            }
        }
    }

    pub fn elim_down(&self, vars: &HashSet<TVar>, tcx: &TypeContext) -> Type {
        println!("⇓ {}", self);
        match self {
            Type::Top => Type::Top,
            Type::Bot => Type::Bot,
            Type::Var(v) => {
                if vars.contains(v) {
                    Type::Bot
                } else {
                    Type::Var(v.clone())
                }
            }
            Type::Union(_) => todo!(),
            Type::Func(f) => {
                let params = f.params.iter().map(|p| p.elim_up(vars, tcx)).collect();
                let ret_ty = f.ret_ty.elim_down(vars, tcx);
                Type::Func(TFunc {
                    params,
                    ret_ty: Box::new(ret_ty),
                })
            }
            Type::All(t) => {
                if t.tyvars.iter().all(|(_, bounds)| {
                    bounds
                        .as_ref()
                        .map(|tys| {
                            tys.iter().all(|t| {
                                if let Type::Var(v) = t {
                                    !vars.contains(v)
                                } else {
                                    true
                                }
                            })
                        })
                        .unwrap_or(true)
                }) {
                    return Type::All(TAll {
                        tyvars: t.tyvars.clone(),
                        ty: Box::new(t.ty.elim_down(vars, tcx)),
                    });
                }
                Type::Bot
            }
        }
    }

    fn apply_subst(self, tv: &TVar, ty: &Type) -> Type {
        match self {
            Type::Top => Type::Top,
            Type::Bot => Type::Bot,
            Type::Var(v) if tv == &v => ty.clone(),
            Type::Union(tys) => Type::Union(tys.into_iter().map(|t| t.apply_subst(tv, ty)).collect()),
            Type::Func(f) => Type::Func(TFunc {
                params: f.params.into_iter().map(|t| t.apply_subst(tv, ty)).collect(),
                ret_ty: Box::new(f.ret_ty.apply_subst(tv, ty)),
            }),
            Type::All(a) => Type::All(TAll {
                tyvars: a.tyvars,
                ty: Box::new(a.ty.apply_subst(tv, ty)),
            }),
            _ => self
        }

        // ty_var, mapped_ty = sub
        // if ty == TOP or ty == BOT:
        //     return ty
        // elif isinstance(ty, TVar):
        //     return mapped_ty if ty_var == ty else TVar(ty.name, ty.bounds)
        // elif isinstance(ty, TAll):
        //     new_ty = TAll(list(ty.vs), [None] * len(ty.ts), None, name=ty.name)
        //     for i, t in enumerate(ty.ts):
        //         new_ty.ts[i] = apply_subst(sub, t, cache)
        //     if ty.t is not None:
        //         new_ty.t = apply_subst(sub, ty.t, cache)
        //     return new_ty

        // raise NotImplementedError(f'ty: {ty}')
    }

    pub fn apply_substs(&self, subst: &HashMap<TVar, Type>) -> Type {
        let mut result_ty = self.clone();
        for (tv, ty) in subst {
            result_ty = result_ty.apply_subst(tv, ty);
        }
        result_ty
    }

    pub fn variance(&self, other: &Type) -> Variance {
        match (self, other) {
            (_, Type::Top) | (_, Type::Bot) => Variance::Constant,
            (_, Type::Var(_)) => {
                if self == other {
                    Variance::Covariant
                } else {
                    Variance::Constant
                }
            },
            (_, Type::Func(f)) => {
                let mut curr = self.variance(&f.ret_ty).invert();
                for ty in f.params.iter() {
                    if ty != other {
                        curr = curr.concat(self.variance(ty));
                    }
                }
                curr
            }
            (Type::All(a), Type::All(b)) => {
                a.ty.variance(&b.ty)
            }
            _ => Variance::Invariant
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TVar(pub String);

impl std::fmt::Display for TVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// impl TVar {
//     pub fn map_bounds<F, T>(&self, f: F) -> Option<T>
//     where
//         F: FnMut(&Vec<Type>) -> T,
//     {
//         self.bounds.as_ref().map(f)
//     }

//     pub fn any_bounds<F>(&self, f: F) -> bool
//     where
//         F: FnMut(&Type) -> bool,
//     {
//         self.bounds
//             .as_ref()
//             .map(|bounds| bounds.iter().any(f))
//             .unwrap_or_default()
//     }
// }

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TFunc {
    pub params: Vec<Type>,
    pub ret_ty: Box<Type>,
}

impl std::fmt::Display for TFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.params
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.ret_ty
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TAll {
    pub tyvars: Vec<(TVar, Option<Vec<Type>>)>,
    pub ty: Box<Type>,
}

impl std::fmt::Display for TAll {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "forall {} . {}",
            self.tyvars
                .iter()
                .map(|(t, b)| if let Some(b) = b {
                    if b.len() == 1 {
                        format!("{} <: {}", t, b[0])
                    } else {
                        format!(
                            "{} <: ({})",
                            t,
                            b.iter()
                                .map(|a| a.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                } else {
                    t.to_string()
                })
                .collect::<Vec<_>>()
                .join(", "),
            self.ty
        )
    }
}
