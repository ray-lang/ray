use std::fmt::{Debug, Display};

use crate::{
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{ShowQuantors, Sigma, Subst, Substitutable, Ty},
    util::Join,
    SigmaPredicates, TyVar,
};

use super::{Constraint, EqualityConstraint, PolyTypeConstraintInfo, Solvable};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolyConstraintKind<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    Generalize(V, Vec<T>, T),
    Instantiate(T, SigmaPredicates<T, V>),
    Skolemize(T, Vec<T>, SigmaPredicates<T, V>),
    Implicit(T, Vec<T>, T),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolymorphismConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) kind: PolyConstraintKind<T, V>,
    pub(crate) info: I,
}

impl<I, T, V> Display for PolymorphismConstraint<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => {
                write!(
                    f,
                    "{} := Generalize([{}], {})",
                    var,
                    mono_tys.free_vars().iter().join(", "),
                    ty,
                )
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                write!(f, "{} := Instantiate({})", ty, sigma.show_quantors())
            }
            PolyConstraintKind::Skolemize(ty, monos, sigma) => {
                write!(
                    f,
                    "{} := Skolemize([{}], {})",
                    ty,
                    monos.free_vars().iter().join(", "),
                    sigma.show_quantors()
                )
            }
            PolyConstraintKind::Implicit(a, monos, b) => {
                write!(
                    f,
                    "{} := Implicit([{}], {})",
                    a,
                    monos.free_vars().iter().join(", "),
                    b,
                )
            }
        }?;

        write!(f, " : {{{}}}", self.info)
    }
}

impl<I, T, V> Substitutable<V, T> for PolymorphismConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        match &mut self.kind {
            PolyConstraintKind::Generalize(_, mono_tys, ty) => {
                for ty in mono_tys {
                    ty.apply_subst(subst);
                }
                ty.apply_subst(subst);
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                ty.apply_subst(subst);
                sigma.apply_subst(subst);
            }
            PolyConstraintKind::Skolemize(ty, monos, sigma) => {
                ty.apply_subst(subst);
                for ty in monos {
                    ty.apply_subst(subst);
                }
                sigma.apply_subst(subst);
            }
            PolyConstraintKind::Implicit(a, monos, b) => {
                a.apply_subst(subst);
                for ty in monos {
                    ty.apply_subst(subst);
                }
                b.apply_subst(subst);
            }
        }
    }

    fn apply_subst_all(&mut self, subst: &Subst<V, T>) {
        match &mut self.kind {
            PolyConstraintKind::Generalize(_, mono_tys, ty) => {
                for ty in mono_tys {
                    ty.apply_subst_all(subst);
                }
                ty.apply_subst_all(subst);
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                ty.apply_subst_all(subst);
                sigma.apply_subst_all(subst);
            }
            PolyConstraintKind::Skolemize(ty, monos, sigma) => {
                ty.apply_subst_all(subst);
                for ty in monos {
                    ty.apply_subst_all(subst);
                }
                sigma.apply_subst_all(subst);
            }
            PolyConstraintKind::Implicit(a, monos, b) => {
                a.apply_subst_all(subst);
                for ty in monos {
                    ty.apply_subst_all(subst);
                }
                b.apply_subst_all(subst);
            }
        }
    }

    fn free_vars(&self) -> Vec<&V> {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => mono_tys
                .free_vars()
                .into_iter()
                .chain(ty.free_vars())
                .chain(std::iter::once(var))
                .collect(),
            PolyConstraintKind::Instantiate(ty, sigma) => ty
                .free_vars()
                .into_iter()
                .chain(sigma.free_vars())
                .collect(),
            PolyConstraintKind::Skolemize(ty, monos, sigma) => ty
                .free_vars()
                .into_iter()
                .chain(monos.free_vars())
                .chain(sigma.free_vars())
                .collect(),
            PolyConstraintKind::Implicit(a, monos, b) => a
                .free_vars()
                .into_iter()
                .chain(monos.free_vars())
                .chain(b.free_vars())
                .collect(),
        }
    }
}

impl<State, I, T, V> Solvable<State, T, V> for PolymorphismConstraint<I, T, V>
where
    State: HasBasic<I, T, V> + HasTypeInference<I, T, V> + HasSubst<I, T, V> + HasQual<I, T, V>,
    I: Debug + Display + Clone + PolyTypeConstraintInfo<I, T, V>,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn solve(&mut self, state: &mut State) {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => {
                state.context_reduction();
                let mut mono_tys = mono_tys.clone();
                let mut ty = ty.clone();
                mono_tys.apply_subst_from(state);
                ty.apply_subst_from(state);
                state.change_qualifiers(|this, qual| qual.apply_subst_from(this));
                log::debug!("mono_tys: {:?}", mono_tys);
                let type_scheme = state.generalize_with_qualifiers(&mono_tys, &ty);
                log::debug!("generalized: {} --> {}", ty, type_scheme);
                state.store_type_scheme(var.clone(), type_scheme);
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                let scheme = state.find_scheme(sigma).unwrap();
                let mut info = self.info.clone();
                info.instantiated_type_scheme(&scheme);
                log::debug!("instantiated type scheme: {:?} ({})", scheme, info);
                if let Some(var) = ty.maybe_var() {
                    state.instantiated_type_scheme(var.clone(), scheme.clone());
                }
                let (preds, instantiated_ty) = state.instantiate(scheme).split();
                log::debug!("preds: {:?}", preds);
                log::debug!("instantiated type: {:?}", instantiated_ty);
                info.equality_type_pair(&instantiated_ty, ty);
                state.prove_qualifiers(preds, &info);
                state.push_constraint(Constraint::from(EqualityConstraint::new(
                    instantiated_ty,
                    ty.clone(),
                    info,
                )));
            }
            PolyConstraintKind::Skolemize(ty, mono_tys, sigma) => {
                let mut info = self.info.clone();
                let forall = state.find_scheme(sigma).unwrap();
                log::debug!("pre-skolemized: {:?}", forall);
                info.skolemized_type_scheme(mono_tys, &forall);
                let (preds, skolem_ty) = state
                    .skolemize_faked(info.clone(), mono_tys.clone(), forall)
                    .split();

                log::debug!("skolemized: {:?}", skolem_ty);
                info.equality_type_pair(ty, ty);
                state.assume_qualifiers(preds, &info);
                state.push_constraint(Constraint::from(EqualityConstraint::new(
                    ty.clone(),
                    skolem_ty,
                    info,
                )));
            }
            PolyConstraintKind::Implicit(lhs, mono_tys, rhs) => {
                let sigma_var = state.get_unique();
                let gen_constraint = PolymorphismConstraint::generalize(
                    V::from_u32(sigma_var),
                    mono_tys.clone(),
                    rhs.clone(),
                    self.info.clone(),
                );
                let inst_constraint = PolymorphismConstraint::instantiate(
                    lhs.clone(),
                    Sigma::Var(V::from_u32(sigma_var)),
                    self.info.clone(),
                );

                // the order of the constraints here matters!
                state.push_constraints(vec![
                    Constraint::from(inst_constraint),
                    Constraint::from(gen_constraint),
                ]);
            }
        }
    }
}

impl<I, T, V> PolymorphismConstraint<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn generalize(
        svar: V,
        mono_tys: Vec<T>,
        ty: T,
        info: I,
    ) -> PolymorphismConstraint<I, T, V> {
        PolymorphismConstraint {
            kind: PolyConstraintKind::Generalize(svar, mono_tys, ty),
            info,
        }
    }

    pub fn instantiate(
        ty: T,
        sigma: SigmaPredicates<T, V>,
        info: I,
    ) -> PolymorphismConstraint<I, T, V> {
        PolymorphismConstraint {
            kind: PolyConstraintKind::Instantiate(ty, sigma),
            info,
        }
    }

    pub fn skolemize(
        ty: T,
        mono_tys: Vec<T>,
        sigma: SigmaPredicates<T, V>,
        info: I,
    ) -> PolymorphismConstraint<I, T, V> {
        PolymorphismConstraint {
            kind: PolyConstraintKind::Skolemize(ty, mono_tys, sigma),
            info,
        }
    }

    pub fn implicit(lhs: T, mono_tys: Vec<T>, rhs: T, info: I) -> PolymorphismConstraint<I, T, V> {
        PolymorphismConstraint {
            kind: PolyConstraintKind::Implicit(lhs, mono_tys, rhs),
            info,
        }
    }
}
