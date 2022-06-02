use std::{
    collections::HashMap,
    ops::{Deref, DerefMut},
};

use crate::{interface::subst::HasSubst, types::Ty};

use super::ForAll;

pub trait Substitutable {
    fn apply_subst(&mut self, subst: &Subst);

    fn apply_subst_from<S, Info>(&mut self, state: &S)
    where
        S: HasSubst<Info>,
    {
        let vars = self.free_vars();
        let tys = vars
            .iter()
            .flat_map(|var| state.find_subst_for_var(*var).cloned())
            .collect::<Vec<_>>();
        let subst = vars.into_iter().zip(tys.into_iter()).collect::<Subst>();
        self.apply_subst(&subst);
    }

    fn free_vars(&self) -> Vec<u32>;

    fn freeze_free_vars(&mut self) {
        let mut subst = Subst::new();
        for var in self.free_vars() {
            subst.insert(var, Ty::Const(format!("_{}", var)));
        }
        self.apply_subst(&subst);
    }

    fn bind_tyvars(self, vars: &[u32]) -> ForAll<Self>
    where
        Self: Sized,
    {
        let free_vars = self.free_vars();
        let vars = vars
            .iter()
            .filter(|var| free_vars.contains(var))
            .cloned()
            .collect();
        ForAll {
            vars,
            quantor_map: HashMap::new(),
            ty: self,
        }
    }

    fn skolemize_free_vars(&mut self) {
        let subst = self
            .free_vars()
            .into_iter()
            .map(|i| (i, Ty::skolem(i)))
            .collect::<Subst>();
        self.apply_subst(&subst);
    }

    #[inline(always)]
    fn quantify(self, vars: &[u32]) -> ForAll<Self>
    where
        Self: Sized,
    {
        self.bind_tyvars(vars)
    }

    fn generalize<Ctx>(self, ctx: &Ctx) -> ForAll<Self>
    where
        Self: Sized,
        Ctx: Substitutable,
    {
        let ctx_freevars = ctx.free_vars();
        let vars = self
            .free_vars()
            .into_iter()
            .filter(|var| !ctx_freevars.contains(var))
            .collect::<Vec<_>>();
        self.quantify(&vars)
    }

    fn generalize_all(self) -> ForAll<Self>
    where
        Self: Sized,
    {
        let vars = self.free_vars();
        self.quantify(&vars)
    }
}

impl<T> Substitutable for Vec<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        for ty in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        self.iter().flat_map(|ty| ty.free_vars()).collect()
    }
}

impl<T, U> Substitutable for (T, U)
where
    T: Substitutable,
    U: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        self.0.apply_subst(subst);
        self.1.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<u32> {
        self.0
            .free_vars()
            .into_iter()
            .chain(self.1.free_vars())
            .collect()
    }
}

impl<T> Substitutable for Option<T>
where
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        if let Some(ty) = self {
            ty.apply_subst(subst);
        }
    }

    fn free_vars(&self) -> Vec<u32> {
        match self {
            Some(ty) => ty.free_vars(),
            None => vec![],
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct Subst(HashMap<u32, Ty>);

impl Deref for Subst {
    type Target = HashMap<u32, Ty>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Subst {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl IntoIterator for Subst {
    type Item = (u32, Ty);
    type IntoIter = <HashMap<u32, Ty> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl FromIterator<(u32, Ty)> for Subst {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (u32, Ty)>,
    {
        let mut subst = Subst::new();
        for (var, ty) in iter {
            subst.insert(var, ty);
        }
        subst
    }
}

impl Subst {
    pub fn new() -> Self {
        Subst(HashMap::new())
    }

    pub fn single(var: u32, ty: Ty) -> Self {
        let mut subst = Subst::new();
        subst.insert(var, ty);
        subst
    }

    pub fn lookup_var(&self, var: u32) -> Option<&Ty> {
        self.get(&var)
    }

    pub fn remove_domain(&mut self, vars: &[u32]) {
        for var in vars {
            self.remove(var);
        }
    }

    pub fn restrict_domain(&mut self, vars: &[u32]) {
        self.retain(|&var, _| vars.contains(&var));
    }
}
