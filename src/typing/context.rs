use std::collections::{HashMap, HashSet};

use super::{
    top::traits::HasFreeVars,
    ty::{Ty, TyVar},
    InferError, Subst,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctx {
    vars: HashMap<String, Ty>,
    ty_vars: HashSet<TyVar>,
    struct_tys: HashMap<String, Vec<(String, Ty)>>,
    pub subst: Subst,
}

impl Ctx {
    pub fn new() -> Ctx {
        Ctx {
            vars: HashMap::new(),
            ty_vars: HashSet::new(),
            struct_tys: HashMap::new(),
            subst: Subst::new(),
        }
    }

    pub fn overwrite_var<S: ToString>(&mut self, name: S, ty: Ty) {
        self.vars.insert(name.to_string(), ty);
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

    pub fn get_var(&self, name: &String) -> Option<&Ty> {
        self.vars.get(name)
    }

    pub fn try_get_var<T: Copy + Clone>(
        &self,
        name: &String,
        metadata: Option<T>,
    ) -> Result<Ty, InferError<T>> {
        self.vars.get(name).cloned().ok_or_else(|| InferError {
            msg: format!("`{}` is undefined", name),
            metadata,
        })
    }

    pub fn free_vars(&self) -> HashSet<&TyVar> {
        let fv = self
            .vars
            .values()
            .flat_map(|t| t.free_vars())
            .collect::<HashSet<_>>();
        fv.difference(&self.ty_vars.iter().collect())
            .map(|t| *t)
            .collect()
    }

    pub fn add_ty_var(&mut self, tv: TyVar) {
        self.ty_vars.insert(tv);
    }

    pub fn get_struct_ty(&mut self, name: &String) -> Option<&Vec<(String, Ty)>> {
        self.struct_tys.get(name)
    }

    pub fn add_struct_ty(&mut self, name: String, fields: Vec<(String, Ty)>) {
        self.struct_tys.insert(name, fields);
    }
}
