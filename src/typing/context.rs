use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::{
    ast::{Node, Path},
    collections::nametree::NameTree,
};

use super::{
    predicate::PredicateEntails,
    state::TyVarFactory,
    traits::HasFreeVars,
    ty::{ImplTy, StructTy, TraitTy, Ty, TyVar},
    ApplySubst, ApplySubstMut, Subst,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TyCtx {
    ty_map: HashMap<u64, Ty>,
    original_ty_map: HashMap<u64, Ty>,
    fqns: HashMap<String, (Path, Option<Path>)>,
    infix_ops: HashMap<String, (Path, Path)>,
    prefix_ops: HashMap<String, (Path, Path)>,
    vars: HashMap<String, Ty>,
    struct_tys: HashMap<Path, StructTy>,
    traits: HashMap<Path, TraitTy>,
    impls: HashMap<Path, Vec<ImplTy>>,
    tf: TyVarFactory,
    sf: TyVarFactory,
    nametree: NameTree,
}

impl ApplySubst for TyCtx {
    fn apply_subst(mut self, subst: &Subst) -> Self {
        for ty in self.ty_map.values_mut() {
            ty.apply_subst_mut(subst);
        }
        self
    }
}

impl HasFreeVars for TyCtx {
    fn free_vars(&self) -> HashSet<&TyVar> {
        self.vars
            .iter()
            .filter_map(|(_, t)| if let Ty::Var(v) = t { Some(v) } else { None })
            .collect()
    }
}

impl TyCtx {
    pub fn new() -> Self {
        Self {
            original_ty_map: HashMap::new(),
            ty_map: HashMap::new(),
            fqns: HashMap::new(),
            infix_ops: HashMap::new(),
            prefix_ops: HashMap::new(),
            vars: HashMap::new(),
            struct_tys: HashMap::new(),
            traits: HashMap::new(),
            impls: HashMap::new(),
            tf: TyVarFactory::new("?t"),
            sf: TyVarFactory::new("#"),
            nametree: NameTree::new(),
        }
    }

    pub fn extend(&mut self, other: TyCtx) {
        self.original_ty_map.extend(other.original_ty_map);
        self.ty_map.extend(other.ty_map);
        self.fqns.extend(other.fqns);
        self.infix_ops.extend(other.infix_ops);
        self.prefix_ops.extend(other.prefix_ops);
        self.struct_tys.extend(other.struct_tys);
        self.traits.extend(other.traits);
        self.impls.extend(other.impls);
        self.nametree.extend(other.nametree);
    }

    pub fn ty_of(&self, id: u64) -> Ty {
        self.ty_map.get(&id).unwrap().clone()
    }

    pub fn maybe_ty_of(&self, id: u64) -> Option<&Ty> {
        self.ty_map.get(&id)
    }

    pub fn original_ty_of<T>(&self, node: &Node<T>) -> Ty {
        self.original_ty_map.get(&node.id).unwrap().clone()
    }

    pub fn set_ty(&mut self, id: u64, ty: Ty) {
        self.original_ty_map.insert(id, ty.clone());
        self.ty_map.insert(id, ty);
    }

    pub fn mk_tvar(&mut self, id: u64) -> Ty {
        let ty = Ty::Var(self.tf().next());
        self.set_ty(id, ty.clone());
        ty
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

    pub fn resolve_name(&self, scopes: &Vec<Path>, name: &String) -> Option<Path> {
        let scopes = scopes.iter().map(Path::to_vec).collect::<Vec<_>>();
        self.nametree.find_in_scopes(&scopes, name).map(|parts| {
            let mut parts = parts.clone();
            parts.push(name.clone());
            Path::from(parts)
        })
    }

    pub fn resolve_path(&self, scopes: &Vec<Path>, path: &Path) -> Option<Path> {
        let scopes = scopes.iter().map(Path::to_vec).collect::<Vec<_>>();
        let parts = path.to_vec();
        self.nametree
            .find_from_parts_in_scopes(&scopes, &parts)
            .map(|scope_parts| {
                let mut new_path = Path::from(scope_parts.clone());
                new_path.extend_mut(parts.into_iter());
                new_path
            })
    }

    pub fn lookup_fqn(&self, name: &String) -> Option<&Path> {
        self.fqns.get(name).map(|(p, _)| p)
    }

    pub fn lookup_fqn_with_trait(&self, name: &String) -> Option<&(Path, Option<Path>)> {
        self.fqns.get(name)
    }

    pub fn lookup_infix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.infix_ops.get(name)
    }

    pub fn lookup_prefix_op(&self, name: &String) -> Option<&(Path, Path)> {
        self.prefix_ops.get(name)
    }

    pub fn add_fqn(&mut self, name: String, fqn: Path, trait_fqn: Option<Path>) {
        self.fqns.insert(name, (fqn, trait_fqn));
    }

    pub fn add_infix_op(&mut self, name: String, infix_op: Path, trait_fqn: Path) {
        self.infix_ops.insert(name, (infix_op, trait_fqn));
    }

    pub fn add_prefix_op(&mut self, name: String, prefix_op: Path, trait_fqn: Path) {
        self.prefix_ops.insert(name, (prefix_op, trait_fqn));
    }

    pub fn get_var(&self, name: &String) -> Option<&Ty> {
        self.vars.get(name)
    }

    pub fn get_struct_ty(&self, fqn: &Path) -> Option<&StructTy> {
        self.struct_tys.get(fqn)
    }

    pub fn add_struct_ty(&mut self, name: String, struct_ty: StructTy) {
        let fqn = struct_ty.path.clone();
        self.add_fqn(name, fqn.clone(), None);
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
        log::debug!("super trait: {}", super_trait);
        let fqn = super_trait.get_path().unwrap();
        log::debug!("super fqn: {}", fqn);
        self.traits
            .values()
            .filter_map(|t| {
                for s in t.super_traits.iter() {
                    log::debug!("super trait: {}", s);
                    let p = s.get_path().unwrap();
                    let name = p.name().unwrap();
                    let super_fqn = self.lookup_fqn(&name).unwrap();
                    log::debug!("super fqn: {}", super_fqn);
                    if &fqn == super_fqn {
                        return Some(&t.ty);
                    }
                }
                None
            })
            .collect()
    }

    pub fn get_trait_fn(&self, trait_fqn: &Path, fn_name: &String) -> Option<&Ty> {
        self.get_trait_ty(trait_fqn).and_then(|trait_ty| {
            trait_ty
                .fields
                .iter()
                .find_map(|(field, ty)| if field == fn_name { Some(ty) } else { None })
        })
    }

    pub fn add_trait_ty(&mut self, name: String, trait_ty: TraitTy) {
        let fqn = trait_ty.path.clone();
        self.add_fqn(name, fqn.clone(), None);
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

    pub fn has_member(&self, fqn: &Path, member: &String) -> bool {
        self.get_struct_ty(&fqn)
            .and_then(|struct_ty| Some(&struct_ty.fields))
            .or_else(|| {
                self.get_trait_ty(&fqn)
                    .and_then(|trait_ty| Some(&trait_ty.fields))
            })
            .map(|fields| fields.iter().find(|(f, _)| f == member).is_some())
            .unwrap_or_default()
    }

    pub fn tf(&mut self) -> &mut TyVarFactory {
        &mut self.tf
    }

    pub fn sf(&mut self) -> &mut TyVarFactory {
        &mut self.sf
    }

    pub fn nametree(&self) -> &NameTree {
        &self.nametree
    }

    pub fn nametree_mut(&mut self) -> &mut NameTree {
        &mut self.nametree
    }

    pub fn instance_of(&self, t: &Ty, u: &Ty) -> bool {
        log::debug!("{} instanceof {}", t, u);
        match (t, u) {
            (Ty::All(_, t), Ty::All(_, u)) => {
                let sub = t.mgu(u).unwrap_or_default();
                let t = t.clone().apply_subst(&sub);
                let u = u.clone().apply_subst(&sub);
                self.instance_of(&t, &u)
            }
            (Ty::All(vs, t), _) => {
                let free_vars = u.free_vars();
                self.instance_of(t, u) && vs.iter().all(|v| !free_vars.contains(v))
            }
            (_, Ty::All(_, u)) => {
                let sub = t.mgu(u).unwrap_or_default();
                let t = t.clone().apply_subst(&sub);
                let u = u.clone().apply_subst(&sub);
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
            (Ty::Ptr(t), Ty::Ptr(u)) => self.instance_of(t, u),
            (Ty::Projection(s, xs), Ty::Projection(t, ys)) if s == t && xs.len() == ys.len() => xs
                .iter()
                .zip(ys.iter())
                .all(|(x, y)| self.instance_of(x, y)),
            (Ty::Union(xs), Ty::Union(ys)) if xs.len() == ys.len() => xs
                .iter()
                .zip(ys.iter())
                .all(|(x, y)| self.instance_of(x, y)),
            (Ty::Cast(a, b), Ty::Cast(c, d)) => self.instance_of(a, c) && self.instance_of(b, d),
            // (_, Ty::Var(_)) => true,
            _ => t == u,
        }
    }
}
