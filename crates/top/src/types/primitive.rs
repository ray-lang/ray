use std::{
    fmt::{Debug, Display},
    hash::Hash,
    str::FromStr,
};

use super::{OrderedTypeSynonyms, Substitutable};

pub trait TyVar: Display + Debug + Clone + Hash + Eq + Ord + FromStr {
    fn from_u32(u: u32) -> Self;

    fn get_u32(&self) -> Option<u32>;
}

pub trait Ty<V>: Display + Debug + Clone + Eq + Ord + Hash + Substitutable<V, Self>
where
    V: TyVar,
{
    fn skolem(var: V) -> Self
    where
        V: Display,
    {
        Ty::new(&format!("#{}", var))
    }

    fn new(name: &str) -> Self;

    fn var(v: V) -> Self;

    fn app(lhs: Self, rhs: Self) -> Self;

    fn tuple(tys: Vec<Self>) -> Self;

    fn arrow(lhs: Self, rhs: Self) -> Self {
        Ty::app(Ty::new("->"), Ty::app(lhs, rhs))
    }

    fn func(param_tys: Vec<Self>, ret_ty: Self) -> Self {
        let mut func = ret_ty;

        for param_ty in param_tys.into_iter().rev() {
            func = Ty::arrow(param_ty, func);
        }

        func
    }

    fn maybe_var(&self) -> Option<&V>;

    fn maybe_const(&self) -> Option<&str>;

    fn maybe_app(&self) -> Option<(Self, Vec<Self>)>;

    fn maybe_func(&self) -> Option<(&Vec<Self>, &Self)>;

    fn maybe_tuple(&self) -> Option<&Vec<Self>>;

    fn maybe_union(&self) -> Option<&Vec<Self>>;

    fn maybe_ptr(&self) -> Option<&Self>;

    fn is_tyvar(&self) -> bool;

    fn in_head_normal_form(&self) -> bool;

    fn name(&self) -> &str;

    fn variables(&self) -> Vec<&V>
    where
        V: Ord;

    fn constants(&self) -> Vec<String>;

    fn left_spine(&self) -> (Self, Vec<Self>) {
        if let Some((lhs, rhs)) = self.maybe_app() {
            (lhs, rhs)
        } else {
            (self.clone(), vec![])
        }
    }

    fn eq_with_synonyms(
        &self,
        other: &Self,
        synonyms: &OrderedTypeSynonyms<Self, V>,
    ) -> Option<Self>;

    fn freeze_vars(&self) -> Self
    where
        V: Display;

    fn unfreeze_vars(&self) -> Self
    where
        V: FromStr,
        <V as FromStr>::Err: std::fmt::Debug;
}
