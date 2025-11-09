use std::{collections::HashMap, fmt::Display};

use crate::{
    Predicates, SigmaPredicates, Subst, TyVar,
    constraint::TypeConstraintInfo,
    state::HasState,
    types::{ForAll, OrderedTypeSynonyms, Scheme, Sigma, Substitutable, Ty},
};

use super::{basic::HasBasic, subst::HasSubst};

pub trait HasTypeInference<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn get_unique(&self) -> u32;

    fn set_unique(&mut self, unique: u32);

    fn type_synonyms(&self) -> &OrderedTypeSynonyms<T, V>;

    fn type_synonyms_mut(&mut self) -> &mut OrderedTypeSynonyms<T, V>;

    fn skolems(&self) -> &Vec<(Vec<V>, I, Vec<T>)>;

    fn skolems_mut(&mut self) -> &mut Vec<(Vec<V>, I, Vec<T>)>;

    fn all_type_schemes(&self) -> &HashMap<V, Scheme<Predicates<T, V>, T, V>>;

    fn get_type_scheme(&self, var: &V) -> Option<&Scheme<Predicates<T, V>, T, V>>;

    fn store_type_scheme(&mut self, var: V, type_scheme: Scheme<Predicates<T, V>, T, V>);

    fn instantiated_type_scheme(&mut self, var: V, type_scheme: Scheme<Predicates<T, V>, T, V>);

    fn add_skolem(&mut self, skolem: (Vec<V>, I, Vec<T>)) {
        self.skolems_mut().push(skolem);
    }

    fn instantiate<A>(&mut self, forall: ForAll<A, T, V>) -> A
    where
        A: Substitutable<V, T> + Clone,
    {
        let unique = self.get_unique();
        let (new_unique, ty) = forall.instantiate(unique);
        self.set_unique(new_unique);
        ty
    }

    fn skolemize<A>(&mut self, forall: ForAll<A, T, V>) -> A
    where
        A: Substitutable<V, T> + Clone,
        V: Display,
    {
        let unique = self.get_unique();
        let (new_unique, ty) = forall.skolemize(unique);
        self.set_unique(new_unique);
        ty
    }

    fn skolemize_faked<A>(&mut self, info: I, mono_tys: Vec<T>, forall: ForAll<A, T, V>) -> A
    where
        A: Substitutable<V, T> + Clone,
        I: Clone,
    {
        let unique = self.get_unique();
        let (new_unique, ty) = forall.instantiate(unique);
        let skolem = (
            (unique..(new_unique - 1)).map(|u| V::from_u32(u)).collect(),
            info,
            mono_tys,
        );
        self.add_skolem(skolem);
        self.set_unique(new_unique);
        ty
    }

    fn make_consistent(&mut self)
    where
        Self: HasSubst<I, T, V>,
        V: Eq,
    {
        <Self as HasSubst<I, T, V>>::make_subst_consistent(self);
    }

    fn check_skolems(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + TypeConstraintInfo<I, T, V>,
        V: Ord,
    {
        // remove all the skolems from the state
        let skolems = self.skolems_mut().drain(..).collect::<Vec<_>>();

        // find skolems that are mapped to a type constant
        let (skolems, ty_const_errs): (Vec<_>, Vec<_>) = skolems
            .into_iter()
            .map(|(vars, info, mono_tys)| {
                (
                    vars.iter()
                        .cloned()
                        .zip(vars.iter().map(|var| self.find_subst_for_var(var)))
                        .collect::<Vec<_>>(),
                    info.clone(),
                    mono_tys,
                )
            })
            .partition(|(vars, _, _)| vars.iter().all(|(_, ty)| ty.is_tyvar()));

        let ty_const_errs = ty_const_errs
            .into_iter()
            .map(|(_, info, _)| info)
            .collect::<Vec<_>>();

        // find skolems that are mapped to another skolem
        let mut skolem_const_errs = skolems
            .iter()
            .flat_map(|(vars, info, _)| {
                vars.into_iter()
                    .filter_map(|(_, ty)| {
                        if let Some(var) = ty.maybe_var() {
                            Some((var.clone(), info.clone()))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        skolem_const_errs.sort_by(|(var1, _), (var2, _)| var1.cmp(var2));
        let mut sk_const_err_groups = HashMap::new();
        for (var, info) in skolem_const_errs.into_iter() {
            sk_const_err_groups
                .entry(var)
                .or_insert_with(Vec::new)
                .push(info);
        }

        let skolem_const_errs = sk_const_err_groups
            .into_iter()
            .filter(|(_, infos)| infos.len() > 1)
            .collect::<Vec<_>>();

        let skolems = {
            let skolem_vars = skolem_const_errs
                .iter()
                .map(|(var, _)| var.clone())
                .collect::<Vec<_>>();

            skolems
                .into_iter()
                .filter(|(pairs, _, _)| {
                    pairs
                        .iter()
                        .flat_map(|(_, t)| t.free_vars())
                        .filter(|var| skolem_vars.contains(var))
                        .count()
                        == 0
                })
                .collect::<Vec<_>>()
        };

        // escaping skolem constants
        let (skolems, escaping_skolems) = skolems.into_iter().fold(
            (vec![], vec![]),
            |(mut acc, mut esc), (pairs, info, mono_tys)| {
                let mut mono_tys = mono_tys.clone();
                mono_tys.apply_subst_from(self);

                let mono_free_vars = mono_tys
                    .iter()
                    .flat_map(|ty| ty.free_vars())
                    .collect::<Vec<_>>();

                let pairs_free_vars = pairs
                    .iter()
                    .flat_map(|(_, t)| t.free_vars())
                    .collect::<Vec<_>>();

                let escaped_skolems = mono_free_vars
                    .into_iter()
                    .filter(|var| pairs_free_vars.contains(var))
                    .cloned()
                    .collect::<Vec<_>>();

                if escaped_skolems.is_empty() {
                    // the intersection is empty
                    acc.push((pairs, info, mono_tys));
                } else {
                    let mut info = info.clone();
                    info.escaped_skolems(&escaped_skolems);
                    esc.push(info);
                }

                (acc, esc)
            },
        );

        // store the remaining skolem constants (that are consistent with the current substitution).
        let skolems = skolems
            .into_iter()
            .map(|(vars, info, mono_tys)| {
                (
                    vars.into_iter()
                        .flat_map(|(_, ty)| ty.free_vars().into_iter().cloned().collect::<Vec<_>>())
                        .collect::<Vec<_>>(),
                    info,
                    mono_tys,
                )
            })
            .collect::<Vec<_>>();

        self.skolems_mut().extend(skolems);

        for info in ty_const_errs {
            self.add_labeled_err("skolem versus constant", info);
        }

        for (_, infos) in skolem_const_errs {
            let info = infos.into_iter().next().unwrap();
            self.add_labeled_err("skolem versus skolem", info);
        }

        for info in escaping_skolems {
            self.add_labeled_err("escaping skolem", info);
        }
    }

    fn resolve_scheme_var(
        &self,
        sigma: &SigmaPredicates<T, V>,
    ) -> Option<Scheme<Predicates<T, V>, T, V>> {
        match sigma {
            Sigma::Var(var) => self.get_type_scheme(var).cloned(),
            Sigma::Scheme(scheme) => Some(scheme.clone()),
        }
    }

    fn find_scheme(&self, sigma: &SigmaPredicates<T, V>) -> Option<Scheme<Predicates<T, V>, T, V>> {
        self.resolve_scheme_var(sigma)
    }
}

#[derive(Debug, Default)]
pub struct TypeInferState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) unique: u32,
    pub(crate) type_synonyms: OrderedTypeSynonyms<T, V>,
    pub(crate) skolems: Vec<(Vec<V>, I, Vec<T>)>,
    pub(crate) type_schemes: Subst<V, Scheme<Predicates<T, V>, T, V>>,
    pub(crate) inst_type_schemes: Subst<V, Scheme<Predicates<T, V>, T, V>>,
}

impl<I, T, U, V> HasTypeInference<I, T, V> for U
where
    I: 'static,
    T: Ty<V>,
    U: HasState<TypeInferState<I, T, V>>,
    V: TyVar,
{
    fn get_unique(&self) -> u32 {
        self.state().unique
    }

    fn set_unique(&mut self, unique: u32) {
        self.state_mut().unique = unique;
    }

    fn type_synonyms(&self) -> &OrderedTypeSynonyms<T, V> {
        &self.state().type_synonyms
    }

    fn type_synonyms_mut(&mut self) -> &mut OrderedTypeSynonyms<T, V> {
        &mut self.state_mut().type_synonyms
    }

    fn skolems(&self) -> &Vec<(Vec<V>, I, Vec<T>)> {
        &self.state().skolems
    }

    fn skolems_mut(&mut self) -> &mut Vec<(Vec<V>, I, Vec<T>)> {
        &mut self.state_mut().skolems
    }

    fn all_type_schemes(&self) -> &HashMap<V, Scheme<Predicates<T, V>, T, V>> {
        &self.state().type_schemes
    }

    fn get_type_scheme(&self, var: &V) -> Option<&Scheme<Predicates<T, V>, T, V>> {
        self.state().type_schemes.get(var)
    }

    fn store_type_scheme(&mut self, var: V, type_scheme: Scheme<Predicates<T, V>, T, V>) {
        self.state_mut().type_schemes.insert(var, type_scheme);
    }

    fn instantiated_type_scheme(&mut self, var: V, type_scheme: Scheme<Predicates<T, V>, T, V>) {
        self.state_mut().inst_type_schemes.insert(var, type_scheme);
    }
}
