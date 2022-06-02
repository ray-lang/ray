use std::collections::VecDeque;

use crate::{
    constraint::{EqualityConstraint, Solvable, TypeConstraintInfo},
    directives::TypeClassDirective,
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{ClassEnv, Entailment, Predicate, Subst, Substitutable, Ty},
};

use super::HasState;

#[derive(Debug, Default, Clone)]
pub struct PredicateMap<T> {
    pub(crate) qualifiers: Vec<(Predicate, T)>,
    pub(crate) generalized_qualifiers: Vec<(Predicate, T)>,
    pub(crate) assumptions: Vec<(Predicate, T)>,
}

#[derive(Debug, Default)]
pub struct OverloadingState<T> {
    pub(crate) class_env: ClassEnv,
    pub(crate) predicate_map: PredicateMap<T>,
    pub(crate) type_class_directives: Vec<TypeClassDirective<T>>,
}

impl<T> OverloadingState<T> {
    pub fn qualifiers(&self) -> &[(Predicate, T)] {
        &self.predicate_map.qualifiers
    }

    pub fn qualifiers_mut(&mut self) -> &mut Vec<(Predicate, T)> {
        &mut self.predicate_map.qualifiers
    }

    pub fn generalized_qualifiers(&self) -> &[(Predicate, T)] {
        &self.predicate_map.generalized_qualifiers
    }

    pub fn generalized_qualifiers_mut(&mut self) -> &mut Vec<(Predicate, T)> {
        &mut self.predicate_map.generalized_qualifiers
    }

    pub fn assumptions(&self) -> &[(Predicate, T)] {
        &self.predicate_map.assumptions
    }

    pub fn assumptions_mut(&mut self) -> &mut Vec<(Predicate, T)> {
        &mut self.predicate_map.assumptions
    }
}

impl<S, T> HasQual<T> for S
where
    S: HasState<OverloadingState<T>> + HasTypeInference<T>,
    T: Clone + 'static,
{
    fn prove_qualifier(&mut self, qualifier: Predicate, info: &T) {
        self.state_mut()
            .predicate_map
            .qualifiers
            .push((qualifier, info.clone()));
    }

    fn assume_qualifier(&mut self, qualifier: Predicate, info: &T) {
        self.state_mut()
            .predicate_map
            .assumptions
            .push((qualifier, info.clone()));
    }

    fn change_qualifiers(&mut self, mut f: impl FnMut(&Self, &mut Predicate) -> ()) {
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

    fn all_qualifiers(&self) -> Vec<&Predicate> {
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
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + TypeConstraintInfo<T>,
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
            if !assumptions.entails(predicate, self.type_synonyms(), self.class_env()) {
                i += 1;
            } else {
                new_preds.remove(i);
            }
        }

        self.state_mut().qualifiers_mut().extend(new_preds);
    }

    fn ambiguous_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<T> + HasBasic<T>,
        T: Clone + std::fmt::Display + TypeConstraintInfo<T>,
    {
        let mut errs = vec![];
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifiers()[i];
            if let Ty::Var(v) = &predicate.ty {
                match self.skolems().iter().find(|(vars, ..)| vars.contains(&v)) {
                    Some((_, info, _)) => {
                        errs.push(("predicate missing in signature", info.clone()));
                        continue;
                    }
                    None => {
                        // try the default
                        let defaults = self
                            .directives()
                            .iter()
                            .filter_map(|directive| {
                                if let TypeClassDirective::Default(name, tys, info) = directive {
                                    if name == &predicate.name {
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
                                let subst = Subst::single(*v, ty.clone());
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
                                        EqualityConstraint::new(Ty::Var(*v), ty.clone(), info);
                                    constraint.solve(self);
                                    self.make_subst_consistent();
                                    continue;
                                }
                            }
                        }
                    }
                }
            }

            errs.push(("ambiguous predicate", info.clone()));
        }
    }

    fn class_env(&self) -> &ClassEnv {
        &self.state().class_env
    }

    fn class_env_mut(&mut self) -> &mut ClassEnv {
        &mut self.state_mut().class_env
    }

    fn directives(&self) -> &Vec<TypeClassDirective<T>> {
        &self.state().type_class_directives
    }

    fn directives_mut(&mut self) -> &mut Vec<TypeClassDirective<T>> {
        &mut self.state_mut().type_class_directives
    }
}
