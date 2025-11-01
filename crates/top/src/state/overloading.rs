use std::{
    collections::VecDeque,
    fmt::{Debug, Display},
    marker::PhantomData,
    str::FromStr,
};

use crate::{
    constraint::{EqualityConstraint, Solvable, TypeConstraintInfo},
    directives::TypeClassDirective,
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{ClassEnv, Entailment, Predicate, Subst, Substitutable, Ty},
    TyVar,
};

use super::HasState;

#[derive(Debug, Default, Clone)]
pub struct PredicateMap<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) qualifiers: Vec<(Predicate<T, V>, I)>,
    pub(crate) generalized_qualifiers: Vec<(Predicate<T, V>, I)>,
    pub(crate) assumptions: Vec<(Predicate<T, V>, I)>,
    _phantom: PhantomData<V>,
}

impl<I, T, V> PredicateMap<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn into_iter(self) -> impl Iterator<Item = Predicate<T, V>> {
        self.qualifiers
            .into_iter()
            .chain(self.generalized_qualifiers.into_iter())
            .chain(self.assumptions.into_iter())
            .map(|(p, _)| p)
    }
}

#[derive(Debug, Default)]
pub struct OverloadingState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) class_env: ClassEnv<T, V>,
    pub(crate) predicate_map: PredicateMap<I, T, V>,
    pub(crate) type_class_directives: Vec<TypeClassDirective<I, T, V>>,
    _phantom: PhantomData<V>,
}

impl<I, T, V> OverloadingState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn qualifiers(&self) -> &[(Predicate<T, V>, I)] {
        &self.predicate_map.qualifiers
    }

    pub fn qualifier(&self, index: usize) -> &(Predicate<T, V>, I) {
        &self.predicate_map.qualifiers[index]
    }

    pub fn qualifiers_mut(&mut self) -> &mut Vec<(Predicate<T, V>, I)> {
        &mut self.predicate_map.qualifiers
    }

    pub fn generalized_qualifiers(&self) -> &[(Predicate<T, V>, I)] {
        &self.predicate_map.generalized_qualifiers
    }

    pub fn generalized_qualifiers_mut(&mut self) -> &mut Vec<(Predicate<T, V>, I)> {
        &mut self.predicate_map.generalized_qualifiers
    }

    pub fn assumptions(&self) -> &[(Predicate<T, V>, I)] {
        &self.predicate_map.assumptions
    }

    pub fn assumptions_mut(&mut self) -> &mut Vec<(Predicate<T, V>, I)> {
        &mut self.predicate_map.assumptions
    }
}

impl<I, S, T, V> HasQual<I, T, V> for S
where
    I: Clone + 'static,
    S: HasState<OverloadingState<I, T, V>> + HasTypeInference<I, T, V>,
    T: Ty<V>,
    V: TyVar,
    <V as FromStr>::Err: Debug,
{
    fn prove_qualifier(&mut self, qualifier: Predicate<T, V>, info: &I) {
        log::debug!("prove qualifier: {}", qualifier);
        self.state_mut()
            .predicate_map
            .qualifiers
            .push((qualifier, info.clone()));
    }

    fn assume_qualifier(&mut self, qualifier: Predicate<T, V>, info: &I) {
        self.state_mut()
            .predicate_map
            .assumptions
            .push((qualifier, info.clone()));
    }

    fn change_qualifiers(&mut self, mut f: impl FnMut(&Self, &mut Predicate<T, V>) -> ()) {
        macro_rules! change_qualifiers {
            ($qualifiers:ident) => {
                let mut qualifiers = self
                    .state_mut()
                    .predicate_map
                    .$qualifiers
                    .drain(..)
                    .collect::<Vec<_>>();
                for (qualifier, _) in qualifiers.iter_mut() {
                    f(self, qualifier);
                }
                self.state_mut()
                    .predicate_map
                    .$qualifiers
                    .extend(qualifiers.into_iter());
            };
        }

        change_qualifiers!(qualifiers);
        change_qualifiers!(generalized_qualifiers);
        change_qualifiers!(assumptions);
    }

    fn all_qualifiers(&self) -> Vec<&Predicate<T, V>> {
        let state = self.state();
        state
            .predicate_map
            .qualifiers
            .iter()
            .map(|(qualifier, _)| qualifier)
            .chain(
                state
                    .predicate_map
                    .generalized_qualifiers
                    .iter()
                    .map(|(qualifier, _)| qualifier),
            )
            .chain(
                state
                    .predicate_map
                    .assumptions
                    .iter()
                    .map(|(qualifier, _)| qualifier),
            )
            .collect()
    }

    fn simplify_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Debug + Clone + TypeConstraintInfo<I, T, V>,
    {
        let predicates = self
            .state_mut()
            .predicate_map
            .qualifiers
            .drain(..)
            .collect();

        let mut new_preds = self.simplify(predicates);
        let mut i = 0;
        let assumptions = self
            .state()
            .assumptions()
            .iter()
            .map(|(a, _)| a)
            .collect::<Vec<_>>();
        while i < new_preds.len() {
            let (predicate, _) = &new_preds[i];
            if predicate.is_record_qualifier()
                || !assumptions.entails(predicate, self.type_synonyms(), self.class_env())
            {
                i += 1;
            } else {
                log::debug!("removing predicate: {}", predicate);
                new_preds.remove(i);
            }
        }

        self.state_mut().qualifiers_mut().extend(new_preds);
    }

    fn default_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Display + Clone + TypeConstraintInfo<I, T, V>,
    {
        for i in 0..self.state().qualifiers().len() {
            log::debug!("--- default_qualifiers iteration {} ---", i);
            log::debug!("predicate = {:?}", self.state().qualifier(i).0);

            let (predicate, _) = &self.state().qualifier(i);
            let ty = match predicate {
                Predicate::Class(_, ty, _) => ty,
                _ => continue,
            };

            let var = match ty.maybe_var() {
                None => {
                    log::debug!("predicate has no type variable, skipping: {}", predicate);
                    continue;
                }
                Some(v) => v,
            };

            if self
                .skolems()
                .iter()
                .find(|(vars, ..)| vars.contains(var))
                .is_some()
            {
                log::debug!(
                    "skipping default for predicate {} because it contains a skolem variable {:?}",
                    predicate,
                    var
                );
                // ignore this predicate since it contains a skolem variable
                continue;
            }

            log::debug!("trying default candidates for {}", predicate);

            // try the default
            let defaults = self
                .directives()
                .iter()
                .filter_map(|directive| {
                    if let TypeClassDirective::Default(name, tys, info) = directive {
                        if matches!(predicate, Predicate::Class(pred_name, _, _) if pred_name == name) {
                            return Some((tys, info));
                        }
                    }

                    None
                })
                .collect::<Vec<_>>();

            // if there is exactly one default
            if let &[(tys, info)] = &defaults[..] {
                // find all the possible candidates for the default
                // if they match the predicate, then we have a match
                let mut candidates = tys.iter().fold(VecDeque::new(), |mut acc, ty| {
                    let subst = Subst::single(var.clone(), ty.clone());
                    let mut pred = predicate.clone();
                    pred.apply_subst(&subst);
                    if vec![].entails(&pred, self.type_synonyms(), self.class_env()) {
                        acc.push_back((ty, info.clone()));
                    }
                    acc
                });

                if let Some((ty, info)) = candidates.pop_front() {
                    if candidates.iter().all(|(other_ty, _)| &ty == other_ty) {
                        let mut constraint =
                            EqualityConstraint::new(T::var(var.clone()), ty.clone(), info);
                        constraint.solve(self);
                        self.make_subst_consistent();
                    }
                }
            }
        }
    }

    fn field_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>,
    {
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifier(i);
            let (record_ty, field, field_ty) = match predicate {
                Predicate::HasField(rt, n, ft, _) => (rt, n, ft),
                _ => continue,
            };

            let var = match field_ty.maybe_var() {
                Some(v) if !record_ty.is_tyvar() => v,
                _ => continue,
            };

            if self
                .skolems()
                .iter()
                .find(|(vars, ..)| vars.contains(var))
                .is_some()
            {
                // ignore this predicate since it contains a skolem variable
                continue;
            }

            let predicates = match self.class_env().record_types(field) {
                Some(ps) => ps,
                _ => continue,
            };

            for other_predicate in predicates {
                match predicate.match_with(other_predicate, self.type_synonyms()) {
                    Some(subst) => {
                        let mut field_ty = field_ty.clone();
                        field_ty.apply_subst(&subst);
                        let mut constraint =
                            EqualityConstraint::new(T::var(var.clone()), field_ty, info.clone());
                        constraint.solve(self);
                        self.make_subst_consistent();
                        break;
                    }
                    None => {}
                }
            }
        }
    }

    fn ambiguous_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>,
        T: Display,
        V: Display + Eq,
    {
        let mut errs = vec![];
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifier(i);
            log::debug!("checking predicate: {}", predicate);
            let tys = match predicate {
                Predicate::Class(_, ty, _) => vec![ty],
                Predicate::HasField(record_ty, _, field_ty, _) => vec![record_ty, field_ty],
            };

            for ty in tys {
                let var = match ty.maybe_var() {
                    Some(v) => v,
                    None => continue,
                };

                match self.skolems().iter().find(|(vars, ..)| vars.contains(var)) {
                    Some((_, info, _)) => {
                        errs.push(("predicate missing in signature", info.clone()));
                    }
                    None => {
                        let mut info = info.clone();
                        info.ambiguous_predicate(predicate);
                        errs.push(("ambiguous predicate", info));
                    }
                }
                break;
            }
        }

        for (label, info) in errs {
            self.add_labeled_err(label, info)
        }
    }

    fn class_env(&self) -> &ClassEnv<T, V> {
        &self.state().class_env
    }

    fn class_env_mut(&mut self) -> &mut ClassEnv<T, V> {
        &mut self.state_mut().class_env
    }

    fn directives(&self) -> &Vec<TypeClassDirective<I, T, V>> {
        &self.state().type_class_directives
    }

    fn directives_mut(&mut self) -> &mut Vec<TypeClassDirective<I, T, V>> {
        &mut self.state_mut().type_class_directives
    }
}
