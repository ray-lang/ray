use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use serde::{Deserialize, Serialize};

use crate::{TyVar, interface::subst::HasSubst, types::Ty};

use super::ForAll;

pub trait Substitutable<V, T>
where
    T: Clone,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>);

    fn apply_subst_all(&mut self, subst: &Subst<V, T>);

    fn apply_subst_from<I, S>(&mut self, state: &S)
    where
        S: HasSubst<I, T, V>,
        T: Display,
        V: Display,
        Self: Debug,
    {
        let vars = self.free_vars();
        let tys = vars
            .iter()
            .map(|var| state.find_subst_for_var(var))
            .collect::<Vec<_>>();
        let subst = vars
            .into_iter()
            .cloned()
            .zip(tys.into_iter())
            .collect::<Subst<V, T>>();
        self.apply_subst(&subst);
    }

    fn free_vars(&self) -> Vec<&V> {
        vec![]
    }

    fn freeze_free_vars(&mut self)
    where
        V: Display,
        T: Ty<V>,
    {
        let mut subst = Subst::new();
        for var in self.free_vars() {
            let ty = T::new(&format!("_{}", var));
            subst.insert(var.clone(), ty);
        }
        self.apply_subst(&subst);
    }

    fn bind_tyvars(self, vars: &[V]) -> ForAll<Self, T, V>
    where
        Self: Sized,
        T: Ty<V>,
    {
        let free_vars = self.free_vars();
        let mut vars = vars
            .iter()
            .filter(|var| free_vars.contains(var))
            .cloned()
            .collect::<Vec<_>>();
        vars.sort();
        vars.dedup();

        ForAll {
            vars,
            ty: self,
            _phantom: PhantomData,
        }
    }

    fn skolemize_free_vars(&mut self)
    where
        V: Display,
        T: Ty<V>,
    {
        let subst = self
            .free_vars()
            .into_iter()
            .map(|i| (i.clone(), Ty::skolem(i.clone())))
            .collect::<Subst<V, T>>();
        self.apply_subst(&subst);
    }

    #[inline(always)]
    fn quantify(self, vars: &[V]) -> ForAll<Self, T, V>
    where
        Self: Sized,
        T: Ty<V>,
    {
        self.bind_tyvars(vars)
    }

    fn generalize_in_ctx<Ctx>(self, ctx: &Ctx) -> ForAll<Self, T, V>
    where
        Self: Sized,
        Ctx: Substitutable<V, T>,
        T: Ty<V>,
    {
        let ctx_freevars = ctx.free_vars();
        let mut vars = self
            .free_vars()
            .into_iter()
            .filter(|var| !ctx_freevars.contains(var))
            .cloned()
            .collect::<Vec<_>>();
        vars.sort();
        vars.dedup();
        self.quantify(&vars)
    }

    fn generalize_all(self) -> ForAll<Self, T, V>
    where
        Self: Sized,
        T: Ty<V>,
    {
        let vars = self.free_vars().into_iter().cloned().collect::<Vec<_>>();
        self.quantify(&vars)
    }
}

impl<A, T, V> Substitutable<V, T> for Vec<A>
where
    A: Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        for ty in self.iter_mut() {
            ty.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        for ty in self.iter_mut() {
            ty.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        self.iter().flat_map(|ty| ty.free_vars()).collect()
    }
}

impl<A, T, V> Substitutable<V, T> for Option<A>
where
    A: Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        if let Some(ty) = self {
            ty.apply_subst(subst);
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        if let Some(ty) = self {
            ty.apply_subst_all(subst);
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match self {
            Some(ty) => ty.free_vars(),
            None => vec![],
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Subst<V, T>(HashMap<V, T>)
where
    V: TyVar;

impl<V, T> Deref for Subst<V, T>
where
    V: TyVar,
{
    type Target = HashMap<V, T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<V, T> DerefMut for Subst<V, T>
where
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<V, T> IntoIterator for Subst<V, T>
where
    V: TyVar,
{
    type Item = (V, T);
    type IntoIter = <HashMap<V, T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<V, T> FromIterator<(V, T)> for Subst<V, T>
where
    V: TyVar,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (V, T)>,
    {
        let mut subst = Subst::new();
        for (var, ty) in iter {
            subst.insert(var, ty);
        }
        subst
    }
}

impl<V, T> Extend<(V, T)> for Subst<V, T>
where
    T: Clone + Substitutable<V, T>,
    V: TyVar,
{
    fn extend<I>(&mut self, _: I)
    where
        I: IntoIterator<Item = (V, T)>,
    {
        panic!("Do not use Subst::extend. Use Subst::union instead");
    }
}

impl<V, T> Display for Subst<V, T>
where
    V: Display + TyVar,
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_empty() {
            return write!(f, "{{}}");
        }

        write!(f, "{{\n")?;
        let mut lines = self.iter().collect::<Vec<_>>();
        lines.sort_by_key(|(var, _)| var.get_u32().unwrap_or(u32::MAX));

        for (var, ty) in lines {
            write!(f, "  {}: {}\n", var, ty)?;
        }

        write!(f, "}}")
    }
}

impl<V, T> Subst<V, T>
where
    V: TyVar,
{
    pub fn new() -> Self {
        Subst(HashMap::new())
    }

    pub fn single(var: V, ty: T) -> Self {
        let mut subst = Subst::new();
        subst.insert(var, ty);
        subst
    }

    pub fn lookup_var(&self, var: &V) -> T
    where
        T: Ty<V>,
    {
        let tv = T::var(var.clone());
        match self.get(var) {
            Some(t) if t != &tv => {
                let mut t = t.clone();
                t.apply_subst(self);
                t
            }
            _ => tv,
        }
    }

    pub fn remove_domain(&mut self, vars: &[V]) {
        for var in vars {
            self.remove(var);
        }
    }

    pub fn restrict_domain(&mut self, vars: &[V]) {
        self.retain(|var, _| vars.contains(var));
    }

    pub fn union(&mut self, other: Self)
    where
        T: Clone + Substitutable<V, T>,
    {
        for (_, ty) in self.iter_mut() {
            ty.apply_subst(&other);
        }

        for (var, ty) in other {
            if !self.contains_key(&var) {
                self.insert(var, ty);
            }
        }
    }
}
