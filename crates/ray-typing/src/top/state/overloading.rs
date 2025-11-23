use std::{
    collections::{BTreeMap, HashSet, VecDeque},
    fmt::{Debug, Display},
    marker::PhantomData,
    str::FromStr,
};

use crate::top::{
    InfoJoin, RecvKind, TyVar,
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

        // Helper to check whether a predicate has an argument that is sufficiently
        // “groundish” to anchor improvement (i.e. has some rigid/constructor structure).
        fn has_groundish_arg<T, V>(pred: &Predicate<T, V>) -> bool
        where
            T: Ty<V>,
            V: TyVar,
        {
            fn is_groundish_ty<T, V>(ty: &T) -> bool
            where
                T: Ty<V>,
                V: TyVar,
            {
                match ty.maybe_var() {
                    Some(var) => !var.is_meta(),
                    None => true,
                }
            }

            match pred {
                Predicate::Class(_, ty, params, _) => {
                    is_groundish_ty(ty) || params.iter().any(is_groundish_ty)
                }
                Predicate::HasField(record_ty, _, field_ty, _) => {
                    is_groundish_ty(record_ty) || is_groundish_ty(field_ty)
                }
                Predicate::Recv(..) => false, // ignored here
            }
        }

        log::debug!("[improve_qualifiers_by_instance] ---- START");
        let mut iteration = 0usize;
        const MAX_IMPROVEMENT_ITER: usize = 100;
        loop {
            let mut changed = false;
            for index in 0..self.state().qualifiers().len() {
                let (pred, _) = self.state().qualifier(index);
                // Recv predicates are handled in a separate improvement pass.
                if matches!(pred, Predicate::Recv(..)) {
                    log::debug!(
                        "[improve_qualifiers_by_instance] skipping Recv predicate {}",
                        pred
                    );
                    continue;
                }

                // Skip predicates that do not mention any *flexible* type variables.
                let pred_free_vars = pred.free_vars();
                let has_flexible_tvar = self.has_flexible_var(pred_free_vars.clone());
                if !has_flexible_tvar {
                    log::debug!(
                        "[improve_qualifiers_by_instance] predicate does NOT have flexible type variables: {:?}",
                        pred
                    );
                    continue;
                }

                // We only use predicates that have at least one “groundish” argument
                // as improvement hints. Purely-meta predicates are left
                // for defaulting / ambiguity checking.
                if !has_groundish_arg(&pred) {
                    log::debug!(
                        "[improve_qualifiers_by_instance] predicate does NOT have any groundish args: {:?}",
                        pred
                    );
                    continue;
                }

                let pred_var_set = pred_free_vars
                    .iter()
                    .map(|var| (*var).clone())
                    .collect::<HashSet<V>>();

                log::debug!("[improve_qualifiers_by_instance] trying predicate {}", pred);

                let synonyms = self.type_synonyms();
                let class_env = self.class_env();

                if let Some(mut candidates) = class_env.by_instance(&pred, synonyms) {
                    if candidates.len() > 1 {
                        // found multiple candidates
                        log::debug!(
                            "[improve_qualifiers_by_instance] multiple candidates for predicate {}: {:?}",
                            pred,
                            candidates
                        );
                        continue;
                    }

                    if candidates.is_empty() {
                        log::debug!(
                            "[improve_qualifiers_by_instance] no candidates for predicate {}: {:?}",
                            pred,
                            candidates
                        );
                        continue;
                    }

                    let Some((subst, _)) = candidates.pop() else {
                        continue;
                    };

                    // Only keep mappings for flexible (non-rigid) type variables.
                    let orig_subst = subst.clone();
                    let flexible_subst = subst
                        .into_iter()
                        .filter(|(var, _)| pred_var_set.contains(var) && !self.is_rigid(var))
                        .collect::<Subst<V, T>>();

                    if !flexible_subst.is_empty() {
                        log::debug!(
                            "[improve_qualifiers_by_instance] applying flexible_subst={:?} from {}",
                            flexible_subst,
                            pred
                        );
                        let prev_subst = self.get_subst().clone();
                        self.get_subst_mut().union(flexible_subst);
                        if !changed {
                            changed = &prev_subst != self.get_subst()
                        }
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

            iteration += 1;
            if iteration > MAX_IMPROVEMENT_ITER {
                log::warn!(
                    "[improve_qualifiers_by_instance] aborting after {} iterations; remaining qualifiers = {}",
                    iteration,
                    self.state().qualifiers().len()
                );
                break;
            }

            self.make_subst_consistent();
            self.apply_subst_to_qualifiers();
        }

        log::debug!("[improve_qualifiers_by_instance] ---- END");
    }

    fn improve_qualifiers_by_recv(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Debug + Clone + Display + TypeConstraintInfo<I, T, V>,
    {
        log::debug!("[improve_qualifiers_by_recv] ---- START");

        loop {
            let mut changed = false;

            for index in 0..self.state().qualifiers().len() {
                let (pred_ref, info_ref) = self.state().qualifier(index);
                if let Predicate::Recv(kind, expr_ty_ref, param_ty_ref, _) = pred_ref {
                    let info = info_ref.clone();
                    let expr_ty = expr_ty_ref.clone();
                    let param_ty = param_ty_ref.clone();

                    // Compute the "base" type of the receiver expression (strip at most one pointer).
                    let base_ty = match expr_ty.maybe_ptr() {
                        Some(inner) => (*inner).clone(),
                        None => expr_ty.clone(),
                    };

                    // Depending on the receiver kind, determine what the parameter type should be.
                    let target_ty = match kind {
                        RecvKind::Value => base_ty,
                        RecvKind::Ref => Ty::ptr(base_ty),
                    };

                    if param_ty != target_ty {
                        let before_subst = self.get_subst().clone();
                        log::debug!(
                            "[improve_qualifiers_by_recv] Recv improvement unify {} == {}",
                            param_ty,
                            target_ty
                        );
                        self.unify_terms(&info, &param_ty, &target_ty);
                        let after_subst = self.get_subst();
                        if &before_subst != after_subst {
                            changed = true;
                        }
                    }
                }
            }

            if !changed {
                log::debug!("[improve_qualifiers_by_recv] no more changes");
                break;
            }

            self.make_subst_consistent();
            self.apply_subst_to_qualifiers();
        }

        log::debug!("[improve_qualifiers_by_recv] ---- END");
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
                            let after_subst = self.get_subst();
                            if &before_subst != after_subst {
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
        log::debug!("[default_qualifiers] ---- START");
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

            if self.has_skolem_var(var) {
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

        log::debug!("[default_qualifiers] ---- END");
    }

    fn field_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V>,
    {
        log::debug!("[field_qualifiers] ---- START");
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifier(i);
            let (record_ty, field, field_ty) = match predicate {
                Predicate::HasField(rt, n, ft, _) => (rt, n, ft),
                _ => continue,
            };

            log::debug!(
                "[field_qualifiers] record_ty={}, field={}, field_ty={}",
                record_ty,
                field,
                field_ty,
            );

            let var = match field_ty.maybe_var() {
                Some(v) if !record_ty.is_tyvar() => v,
                _ => continue,
            };

            if self.has_skolem_var(var) {
                // ignore this predicate since it contains a skolem variable
                log::debug!(
                    "[field_qualifiers] has skolem variable: skolem={}, record_ty={}, field={}, field_ty={}",
                    var,
                    record_ty,
                    field,
                    field_ty,
                );
                continue;
            }

            let predicates = match self.class_env().record_types(field) {
                Some(ps) => ps,
                _ => {
                    log::debug!(
                        "[field_qualifiers] could not find predicates for record_ty={}, field={}, field_ty={}: class_env={:?}",
                        record_ty,
                        field,
                        field_ty,
                        self.class_env(),
                    );
                    continue;
                }
            };

            log::debug!(
                "[field_qualifiers] predicates with field {}: {:?}",
                field,
                predicates
            );

            for other_predicate in predicates {
                match predicate.match_with(other_predicate, self.type_synonyms()) {
                    Some(subst) => {
                        log::debug!("[field_qualifiers] applying subst: {}", subst);
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
        log::debug!("[field_qualifiers] ---- END");
    }

    fn ambiguous_qualifiers(&mut self)
    where
        Self: Sized + HasSubst<I, T, V> + HasBasic<I, T, V> + HasTypeInference<I, T, V>,
        I: Clone + Display + TypeConstraintInfo<I, T, V> + InfoJoin,
        T: Display,
        V: Display + Eq,
    {
        log::debug!("[ambiguous_qualifiers] ---- START");
        let mut errs = vec![];
        for i in 0..self.state().qualifiers().len() {
            let (predicate, info) = &self.state().qualifier(i);
            log::debug!("checking predicate: {}", predicate);

            if matches!(predicate, Predicate::Recv(..)) {
                log::debug!("[ambiguous_qualifiers] skipping predicate {}", predicate);
                continue;
            }

            let tys = match predicate {
                Predicate::Class(_, ty, params, _) => {
                    std::iter::once(ty).chain(params.iter()).collect()
                }
                Predicate::HasField(record_ty, _, field_ty, _) => vec![record_ty, field_ty],
                Predicate::Recv(..) => {
                    // Recv predicates are internal to method-call resolution and
                    // should not produce ambiguous/missing predicate errors.
                    continue;
                }
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
        log::debug!("[ambiguous_qualifiers] ---- END");
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
