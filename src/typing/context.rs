use std::{
    cell::{RefCell, RefMut},
    collections::{HashMap, HashSet},
    rc::Rc,
};

use crate::{ast::Path, utils::join};

use super::{
    predicate::{PredicateEntails, TyPredicate},
    top::{state::TyVarFactory, traits::HasFreeVars},
    ty::{ImplTy, StructTy, TraitTy, Ty, TyVar},
    ApplySubst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctx {
    fqns: HashMap<String, Path>,
    vars: HashMap<String, Ty>,
    struct_tys: HashMap<Path, StructTy>,
    traits: HashMap<Path, TraitTy>,
    impls: HashMap<Path, Vec<ImplTy>>,
    tf: Rc<RefCell<TyVarFactory>>,
    sf: Rc<RefCell<TyVarFactory>>,
}

impl HasFreeVars for Ctx {
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.vars
            .iter()
            .filter_map(|(_, t)| if let Ty::Var(v) = t { Some(v) } else { None })
            .collect()
    }
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            fqns: HashMap::new(),
            vars: HashMap::new(),
            struct_tys: HashMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            tf: Rc::new(RefCell::new(TyVarFactory::new("?t"))),
            sf: Rc::new(RefCell::new(TyVarFactory::new("#"))),
        }
    }

    pub fn bind_var<S: ToString>(&mut self, name: S, ty: Ty) {
        let s = name.to_string();
        if let Some(other_ty) = self.vars.get_mut(&s) {
            if other_ty.is_func() && !other_ty.has_unknowns() {
                // add `ty` as an overload by converting this into a union
                *other_ty = Ty::Union(vec![other_ty.clone(), ty]);
                return;
            } else if other_ty.is_funcs_union() {
                other_ty.add_to_union(ty);
                return;
            }
        }

        self.vars.insert(s, ty);
    }

    pub fn lookup_fqn(&self, name: &String) -> Option<&Path> {
        self.fqns.get(name)
    }

    pub fn add_fqn(&mut self, name: String, fqn: Path) {
        self.fqns.insert(name, fqn);
    }

    pub fn get_var(&self, name: &String) -> Option<&Ty> {
        self.vars.get(name)
    }

    pub fn get_struct_ty(&mut self, fqn: &Path) -> Option<&StructTy> {
        self.struct_tys.get(fqn)
    }

    pub fn add_struct_ty(&mut self, name: String, struct_ty: StructTy) {
        let fqn = struct_ty.path.clone();
        self.add_fqn(name, fqn.clone());
        self.struct_tys.insert(fqn, struct_ty);
    }

    pub fn get_trait_ty(&self, fqn: &Path) -> Option<&TraitTy> {
        self.traits.get(fqn)
    }

    pub fn get_super_traits_from_ty(&self, ty: &Ty) -> Option<&Vec<Ty>> {
        if let Some(fqn) = ty.get_path() {
            match self.get_trait_ty(&fqn) {
                Some(trait_ty) => Some(&trait_ty.super_traits),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn get_subtraits(&self, super_trait: &Ty) -> Vec<&Ty> {
        let fqn = super_trait.get_path().unwrap();
        self.traits
            .values()
            .filter_map(|t| {
                for s in t.super_traits.iter() {
                    if fqn == s.get_path().unwrap() {
                        return Some(&t.ty);
                    }
                }
                None
            })
            .collect()
    }

    pub fn add_trait_ty(&mut self, name: String, trait_ty: TraitTy) {
        let fqn = trait_ty.path.clone();
        self.add_fqn(name, fqn.clone());
        self.traits.insert(fqn, trait_ty);
    }

    pub fn add_impl(&mut self, trait_fqn: Path, impl_ty: ImplTy) {
        if !self.impls.contains_key(&trait_fqn) {
            self.impls.insert(trait_fqn, vec![impl_ty]);
        } else {
            self.impls.get_mut(&trait_fqn).unwrap().push(impl_ty);
        }
    }

    pub fn get_impls(&self, ty: &Ty) -> Option<&Vec<ImplTy>> {
        let fqn = ty.get_path().unwrap();
        self.impls.get(&fqn)
    }

    fn try_instance(
        &self,
        p: &TyPredicate,
        q: &TyPredicate,
        preds: Vec<&TyPredicate>,
    ) -> Option<Vec<TyPredicate>> {
        if let Some(sub) = p.match_predicate(q) {
            Some(
                preds
                    .into_iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .apply_subst(&sub),
            )
        } else {
            None
        }
    }

    // pub fn by_instance(&self, p: &TyPredicate) -> Vec<TyPredicate> {
    //     // let tryInstance (p',list) = do sub <- matchPredicates synonyms p p'
    //     //                           Just (sub |-> list)
    //     //     in msum [ tryInstance it | it <- instances s classes ]
    //     let trait_ty = match p {
    //         TyPredicate::Trait(_, t) => t,
    //         _ => return vec![],
    //     };

    //     let fqn = trait_ty.get_path().unwrap();
    //     self.impls
    //         .get(&fqn)
    //         .map(|i| {
    //             i.iter()
    //                 .flat_map(|t| {
    //                     let p_prime = TyPredicate::Trait(t.clone(), trait_ty.clone());
    //                     if let Some(sub) = p.match_predicate(&p_prime) {
    //                         Some(p_prime)
    //                     } else {
    //                         None
    //                     }
    //                 })
    //                 .collect::<Vec<_>>()
    //         })
    //         .unwrap_or_default()

    //     // impls.iter().flat_map(|t| {
    //     //     let p_prime = TyPredicate::Trait(t.clone(), trait_ty.clone());
    //     //     if let Some(sub) = p.match_predicate(&p_prime) {
    //     //         Some(p_prime)
    //     //     } else {
    //     //         None
    //     //     }
    //     // });
    //     // } else {
    //     //     vec![]
    //     // }
    // }

    // pub fn by_supertrait(&self, p: &TyPredicate) -> Vec<TyPredicate> {
    //     // p : concat [ bySuperclass classes (Predicate s' tp) | s' <- superclasses s classes ]
    //     let (s, super_traits) = match p {
    //         TyPredicate::Trait(s, t) => match self.get_super_traits_from_ty(t) {
    //             Some(v) => (s, v),
    //             _ => return vec![],
    //         },
    //         _ => return vec![],
    //     };

    //     let super_preds = super_traits
    //         .iter()
    //         .flat_map(|st| match self.get_super_traits_from_ty(st) {
    //             Some(v) => v
    //                 .iter()
    //                 .flat_map(|t| self.by_supertrait(&TyPredicate::Trait(s.clone(), t.clone())))
    //                 .collect(),
    //             _ => vec![],
    //         })
    //         .collect::<Vec<_>>();

    //     let mut preds = vec![p.clone()];
    //     preds.extend(super_preds);
    //     println!("[{}]", join(&preds, ", "));
    //     preds
    // }

    // pub fn implements(&self, base_ty: &Ty, trait_ty: &Ty, preds: &Vec<TyPredicate>) -> bool {
    //     match base_ty {
    //         Ty::Var(_) | Ty::Bound(_) => {
    //             todo!()
    //             // for p in preds {
    //             //     match p {
    //             //         TyPredicate::Trait(v, tr) if base_ty == v && trait == trait_ty => {
    //             //             return true
    //             //         }
    //             //         _ => continue,
    //             //     }
    //             // }
    //             // false
    //         }
    //         Ty::Union(t) => t.iter().all(|t| self.implements(t, trait_ty, preds)),
    //         Ty::Projection(_, _) => {
    //             println!("{} <: {}", base_ty, trait_ty);
    //             if let Ty::Projection(t, _) = trait_ty {
    //                 // this should already be an FQN, just needs to be parsed
    //                 let fqn = Path::from(t);
    //                 println!("fqn = {}", fqn);
    //                 let impls = self.impls.get(&fqn);
    //                 println!("{:?}", impls);
    //                 impls.map_or(false, |tys| {
    //                     tys.iter().any(|t| base_ty.instance_of(t, self))
    //                 })
    //             } else {
    //                 false
    //             }
    //         }
    //         Ty::Cast(_, t) => self.implements(t, trait_ty, preds),
    //         Ty::Qualified(q, t) => self.implements(t, trait_ty, q),
    //         Ty::All(_, t) => self.implements(t, trait_ty, preds),

    //         // functions and never/any cannot implement traits
    //         Ty::Func(_, _) | Ty::Never | Ty::Any => false,
    //     }
    // }

    pub fn tf_mut(&self) -> RefMut<TyVarFactory> {
        self.tf.borrow_mut()
    }

    pub fn sf_mut(&self) -> RefMut<TyVarFactory> {
        self.sf.borrow_mut()
    }

    pub fn new_tvar(&mut self) -> TyVar {
        self.tf_mut().next()
    }

    pub fn new_svar(&mut self) -> TyVar {
        self.sf.borrow_mut().next()
    }

    pub fn instance_of(&self, t: &Ty, u: &Ty) -> bool {
        println!("instance_of: {} < {}", t, u);
        let res = match (t, u) {
            (Ty::All(vs, t), _) => {
                let free_vars = u.free_vars();
                self.instance_of(t, u) && vs.iter().all(|v| !free_vars.contains(v))
            }
            (_, Ty::All(_, u)) => {
                let sub = match t.mgu(u) {
                    Ok(s) => s,
                    _ => return false,
                };
                println!("instance_of: sub = {}", sub);
                let t = t.clone().apply_subst(&sub);
                println!("instance_of: t = {}", t);
                let u = u.clone().apply_subst(&sub);
                println!("instance_of: u = {}", u);
                self.instance_of(&t, &u)
            }
            (Ty::Qualified(p, t), Ty::Qualified(q, u)) => {
                p.entails(q, self) && self.instance_of(t, u)
            }
            (Ty::Qualified(_, t), u) => self.instance_of(t, u),
            (t, Ty::Qualified(p, u)) => vec![].entails(p, self) && self.instance_of(t, u),
            (Ty::Func(p, q), Ty::Func(r, s)) if p.len() == r.len() => {
                p.iter().zip(r.iter()).all(|(x, y)| self.instance_of(x, y))
                    && self.instance_of(q, s)
            }
            (Ty::Projection(s, xs), Ty::Projection(t, ys)) if s == t && xs.len() == ys.len() => xs
                .iter()
                .zip(ys.iter())
                .all(|(x, y)| self.instance_of(x, y)),
            (Ty::Union(xs), Ty::Union(ys)) if xs.len() == ys.len() => xs
                .iter()
                .zip(ys.iter())
                .all(|(x, y)| self.instance_of(x, y)),
            (Ty::Cast(a, b), Ty::Cast(c, d)) => self.instance_of(a, c) && self.instance_of(b, d),
            _ => t == u,
        };

        if res {
            println!("{} is instance of {}", t, u)
        } else {
            println!("{} is NOT instance of {}", t, u)
        }
        res
    }
}
