use std::{
    collections::{BTreeMap, HashSet, VecDeque},
    fmt::{Debug, Display},
    marker::PhantomData,
    str::FromStr,
};

use itertools::Itertools;

use crate::{
    InfoJoin, TyVar,
    constraint::{EqualityConstraint, Solvable, TypeConstraintInfo},
    directives::TypeClassDirective,
    interface::{
        basic::{ErrorLabel, HasBasic},
        qualification::HasQual,
        subst::HasSubst,
        type_inference::HasTypeInference,
    },
    types::{ClassEnv, Entailment, Predicate, Subst, Substitutable, Ty},
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

    fn qualifiers(&self) -> Vec<&Predicate<T, V>> {
        self.state()
            .predicate_map
            .qualifiers
            .iter()
            .map(|(q, _)| q)
            .collect::<Vec<_>>()
    }

    fn generalized_qualifiers(&self) -> Vec<&Predicate<T, V>> {
        self.state()
            .predicate_map
            .generalized_qualifiers
            .iter()
            .map(|(q, _)| q)
            .collect::<Vec<_>>()
    }

    fn assumptions(&self) -> Vec<&Predicate<T, V>> {
        self.state()
            .predicate_map
            .assumptions
            .iter()
            .map(|(q, _)| q)
            .collect::<Vec<_>>()
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
            // If this predicate still contains any *flexible* type vars,
            // do NOT try to discharge it via entails. Leave it for defaults / later passes.
            let has_flexible_tvar = self.has_flexible_var(predicate.free_vars());
            if predicate.is_record_qualifier()
                || has_flexible_tvar
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

    fn improve_qualifiers_by_instance(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>,
    {
        // We run an instance-driven "improvement" step on the current qualifiers.
        // The goal is to use available instances to refine flexible type
        // variables that are already constrained by *concrete* type arguments
        // (for example, Mul[α, uint, uint] should pin α to uint before we
        // fall back to defaulting).
        //
        // We intentionally:
        //   - Only consider predicates that are in head-normal form.
        //   - Only consider predicates that contain at least one flexible
        //     type variable.
        //   - Only consider predicates that have at least one argument that
        //     is fully concrete (no free type variables).
        //
        // This mirrors the "improvement" ideas from qualified types: use
        // instance heads to refine ambiguous type variables, but do not
        // discharge predicates or touch rigid/skolem variables here.

        // Helper to check whether a predicate has at least one fully
        // concrete argument (no free type variables).
        fn has_concrete_arg<T, V>(pred: &Predicate<T, V>) -> bool
        where
            T: Ty<V>,
            V: TyVar,
        {
            let is_concrete = |ty: &T| ty.free_vars().is_empty();

            match pred {
                Predicate::Class(_, ty, params, _) => {
                    is_concrete(ty) || params.iter().any(|p| is_concrete(p))
                }
                Predicate::HasField(record_ty, _, field_ty, _) => {
                    is_concrete(record_ty) || is_concrete(field_ty)
                }
            }
        }

        log::debug!("[improve_qualifiers_by_instance] ---- START");
        loop {
            let mut changed = false;
            for index in 0..self.state().qualifiers().len() {
                let (pred, _) = self.state().qualifier(index);

                // Skip predicates that do not mention any *flexible* type variables.
                let has_flexible_tvar = self.has_flexible_var(pred.free_vars());
                if !has_flexible_tvar {
                    log::debug!(
                        "[improve_qualifiers_by_instance] predicate does NOT have flexible type variables: {:?}",
                        pred
                    );
                    continue;
                }

                // We only use predicates that have at least one concrete argument
                // as "improvement hints". Purely-polymorphic predicates are left
                // for defaulting / ambiguity checking.
                if !has_concrete_arg(&pred) {
                    log::debug!(
                        "[improve_qualifiers_by_instance] predicate does NOT have any concrete args: {:?}",
                        pred
                    );
                    continue;
                }

                log::debug!("[improve_qualifiers_by_instance] trying predicate {}", pred);

                let synonyms = self.type_synonyms();
                let class_env = self.class_env();

                if let Some((subst, _instance_preds)) = class_env.by_instance(&pred, synonyms) {
                    // Only keep mappings for flexible (non-rigid) type variables.
                    let orig_subst = subst.clone();
                    let flexible_subst = subst
                        .into_iter()
                        .filter(|(var, _)| !self.is_rigid(var))
                        .collect::<Subst<V, T>>();

                    if !flexible_subst.is_empty() {
                        log::debug!(
                            "[improve_qualifiers_by_instance] applying flexible_subst={:?} from {}",
                            flexible_subst,
                            pred
                        );
                        let global_subst = self.get_subst_mut();
                        global_subst.union(flexible_subst);
                        changed = true;
                    } else {
                        log::debug!(
                            "[improve_qualifiers_by_instance] flexible subst is empty after by_instance for predicate={:?}, original_subst={:?}",
                            pred,
                            orig_subst
                        );
                    }
                }
            }

            if !changed {
                break;
            }

            self.make_subst_consistent();
            self.apply_subst_to_qualifiers();
        }

        log::debug!("[improve_qualifiers_by_instance] ---- END");
    }

    fn improve_qualifiers_by_receiver(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Debug + Clone + Display + TypeConstraintInfo<I, T, V>,
    {
        log::debug!("[improve_qualifiers_by_receiver] ---- START");

        // iterate qualifiers ("wanted") and assumptions ("given")
        // and group Class predicates by name AND receiver type
        let mut groups: BTreeMap<(String, T), Vec<(T, Vec<T>, I)>> = BTreeMap::new();
        for (predicate, info) in self
            .state()
            .qualifiers()
            .iter()
            .chain(self.state().assumptions().iter())
        {
            let Predicate::Class(name, recv_ty, params, _) = predicate else {
                continue;
            };

            if params.is_empty() {
                // ignore single-parameter classes
                continue;
            }

            groups
                .entry((name.clone(), recv_ty.clone()))
                .or_default()
                .push((recv_ty.clone(), params.clone(), info.clone()))
        }

        loop {
            // iterate over each group and unify the elements
            let mut changed = false;
            for ((class_name, recv_ty), group) in groups.iter() {
                log::debug!(
                    "[improve_qualifiers_by_receiver] group for {}[{}, ..]",
                    class_name,
                    recv_ty,
                );

                for (recv_ty, params, _) in group.iter() {
                    log::debug!(
                        "[improve_qualifiers_by_receiver]     [{}, {}]",
                        recv_ty,
                        params
                            .iter()
                            .map(|p| format!("{:?}", p))
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                }

                for i in 0..group.len() {
                    let (lhs_recv_ty, lhs_params, lhs_info) = &group[i];
                    let mut lhs_recv_ty = lhs_recv_ty.clone();
                    lhs_recv_ty.apply_subst_from(self);

                    let mut lhs_params = lhs_params.clone();
                    lhs_params.apply_subst_from(self);

                    for j in (i + 1)..group.len() {
                        let (rhs_recv_ty, rhs_params, _rhs_info) = &group[j];
                        let mut rhs_recv_ty = rhs_recv_ty.clone();

                        rhs_recv_ty.apply_subst_from(self);

                        if lhs_recv_ty != rhs_recv_ty {
                            // cannot unify with receiver types that are not equal
                            log::debug!(
                                "[improve_qualifiers_by_receiver] cannot unify with receiver types that are not equal: {} != {}",
                                lhs_recv_ty,
                                rhs_recv_ty,
                            );
                            continue;
                        }

                        let mut rhs_params = rhs_params.clone();
                        rhs_params.apply_subst_from(self);

                        for (lhs, rhs) in lhs_params.iter().zip(rhs_params.iter()) {
                            if lhs == rhs
                                || (lhs.free_vars().is_empty() && rhs.free_vars().is_empty())
                            {
                                // ignore types that are already equal or where neither contain free variables
                                log::debug!(
                                    "[improve_qualifiers_by_receiver] ignore types that are already equal or where neither contain free variables: {} and {}",
                                    lhs,
                                    rhs,
                                );
                                continue;
                            }

                            // snapshot the current global subst
                            let before_subst = self.get_subst().clone();

                            // TODO: merge the info together
                            log::debug!(
                                "[improve_qualifiers_by_receiver] unify terms: {} == {}",
                                lhs,
                                rhs,
                            );
                            self.unify_terms(&lhs_info, lhs, rhs);
                            let after_subst = self.get_subst().clone();
                            if before_subst != after_subst {
                                changed = true;
                            }
                        }
                    }
                }
            }

            if !changed {
                log::debug!("[improve_qualifiers_by_receiver] no more changes");
                break;
            }

            self.make_subst_consistent();
            self.apply_subst_to_qualifiers();
        }

        log::debug!("[improve_qualifiers_by_receiver] ---- END");
    }

    fn default_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Display + Clone + TypeConstraintInfo<I, T, V>,
    {
        for i in 0..self.state().qualifiers().len() {
            log::debug!("--- default_qualifiers iteration {} ---", i);
            let (predicate, _) = &self.state().qualifier(i);
            log::debug!("predicate = {:?}", predicate);

            let ty = match predicate {
                Predicate::Class(_, ty, _, _) => ty,
                _ => {
                    log::debug!("not a class predicate");
                    continue;
                }
            };

            let var = match ty.maybe_var() {
                None => {
                    log::debug!("predicate has no type variable, skipping: {}", predicate);
                    continue;
                }
                Some(v) => v,
            };

            if self.is_rigid(var) {
                log::debug!(
                    "skipping default for {:?} because {:?} is rigid",
                    predicate,
                    var
                );
                continue;
            }

            if self
                .skolems()
                .iter()
                .find(|skolem| skolem.contains(var))
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

            let head_vars = ty.free_vars().into_iter().collect::<HashSet<_>>();

            // Does head_vars appear anywhere else?
            let shared = self
                .state()
                .qualifiers()
                .iter()
                .enumerate()
                .any(|(j, (q, _))| {
                    if j == i {
                        return false;
                    }

                    let q_vars = q.free_vars();
                    let found = q_vars.iter().any(|v| head_vars.contains(v));
                    log::debug!(
                        "[default_qualifiers] checked if other predicate {:?} has vars in head vars {:?} => found={}",
                        q,
                        head_vars,
                        found
                    );
                    found
                });

            if shared {
                // This Int[...] is *not* ambiguous, so do not default it.
                log::debug!(
                    "skipping default for predicate {} because it is not ambiguous",
                    predicate,
                );
                continue;
            }

            log::debug!("trying default candidates for {}", predicate);

            // try the default
            let defaults = self
                .directives()
                .iter()
                .filter_map(|directive| {
                    if let TypeClassDirective::Default(name, tys, info) = directive {
                        if matches!(predicate, Predicate::Class(pred_name, _, _, _) if pred_name == name) {
                            return Some((tys, info));
                        }
                    }

                    None
                })
                .collect::<Vec<_>>();

            // if there is exactly one default
            if let &[(tys, info)] = &defaults[..] {
                log::debug!(
                    "found a single default directive: tys={:?}, info={}",
                    tys,
                    info
                );
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
                    log::debug!("found the default candidate: ty={:?}, info={}", ty, info);
                    if candidates.iter().all(|(other_ty, _)| &ty == other_ty) {
                        log::debug!(
                            "creating a equality constraint and solving: {} == {}",
                            var,
                            ty
                        );
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
                .find(|skolem| skolem.contains(var))
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
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V> + HasTypeInference<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V> + InfoJoin,
        T: Display,
        V: Display + Eq,
    {
        let mut errs = vec![];
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifier(i);
            log::debug!("checking predicate: {}", predicate);
            let tys = match predicate {
                Predicate::Class(_, ty, params, _) => {
                    std::iter::once(ty).chain(params.iter()).collect()
                }
                Predicate::HasField(record_ty, _, field_ty, _) => vec![record_ty, field_ty],
            };

            for ty in tys {
                let var = match ty.maybe_var() {
                    Some(v) => v,
                    None => continue,
                };

                if let Some(skolem) = self.skolems().iter().find(|skolem| skolem.contains(var)) {
                    let mut info = info.clone().join(skolem.info.clone());
                    info.missing_predicate(predicate);
                    errs.push((ErrorLabel::MissingPredicate, info));
                } else {
                    let mut info = info.clone();
                    info.ambiguous_predicate(predicate);
                    errs.push((ErrorLabel::AmbiguousPredicate, info));
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
