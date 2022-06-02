use crate::{
    interface::{
        basic::HasBasic, qualification::HasQual, subst::HasSubst, type_inference::HasTypeInference,
    },
    types::{Predicate, ShowQuantors, Sigma, Subst, Substitutable, Ty},
    util::Join,
};

use super::{Constraint, EqualityConstraint, PolyTypeConstraintInfo, Solvable};

#[derive(Debug)]
pub enum PolyConstraintKind {
    Generalize(u32, Vec<Ty>, Ty),
    Instantiate(Ty, Sigma<Vec<Predicate>>),
    Skolemize(Ty, Vec<Ty>, Sigma<Vec<Predicate>>),
    Implicit(Ty, Vec<Ty>, Ty),
}

#[derive(Debug)]
pub struct PolymorphismConstraint<Info> {
    kind: PolyConstraintKind,
    info: Info,
}

impl<Info> std::fmt::Display for PolymorphismConstraint<Info>
where
    Info: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => {
                write!(
                    f,
                    "$s{} := Generalize({})",
                    var,
                    mono_tys
                        .free_vars()
                        .iter()
                        .map(|var| Ty::Var(*var).to_string())
                        .chain(std::iter::once(ty.to_string()))
                        .join(", "),
                )
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                write!(
                    f,
                    "{} := Instantiate({})",
                    ty,
                    sigma.displayable().show_quantors()
                )
            }
            PolyConstraintKind::Skolemize(ty, monos, sigma) => {
                write!(
                    f,
                    "{} := Skolemize({})",
                    ty,
                    monos
                        .free_vars()
                        .iter()
                        .map(|var| Ty::Var(*var).to_string())
                        .chain(std::iter::once(sigma.displayable().show_quantors()))
                        .join(", "),
                )
            }
            PolyConstraintKind::Implicit(a, monos, b) => {
                write!(
                    f,
                    "{} := Implicit({})",
                    a,
                    monos
                        .free_vars()
                        .iter()
                        .map(|var| Ty::Var(*var).to_string())
                        .chain(std::iter::once(b.to_string()))
                        .join(", "),
                )
            }
        }?;

        write!(f, "  : {{ {} }}", self.info)
    }
}

impl<Info> Substitutable for PolymorphismConstraint<Info> {
    fn apply_subst(&mut self, subst: &Subst) {
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

    fn free_vars(&self) -> Vec<u32> {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => mono_tys
                .free_vars()
                .into_iter()
                .chain(ty.free_vars())
                .chain(std::iter::once(*var))
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

impl<State, T> Solvable<State> for PolymorphismConstraint<T>
where
    State: HasBasic<T> + HasTypeInference<T> + HasSubst<T> + HasQual<T>,
    T: std::fmt::Display + Clone + PolyTypeConstraintInfo<T>,
{
    fn solve(&mut self, state: &mut State) {
        match &self.kind {
            PolyConstraintKind::Generalize(var, mono_tys, ty) => {
                state.context_reduction();
                let mut mono_tys = mono_tys.clone();
                let mut ty = ty.clone();
                mono_tys.apply_subst_from(state);
                ty.apply_subst_from(state);
                let type_scheme = state.generalize_with_qualifiers(&mono_tys, &ty);
                state.store_type_scheme(*var, type_scheme);
            }
            PolyConstraintKind::Instantiate(ty, sigma) => {
                let scheme = state.find_scheme(sigma).unwrap();
                self.info.instantiated_type_scheme(&scheme);
                let (preds, instantiated_ty) = state.instantiate(scheme).split();
                self.info.equality_type_pair(&instantiated_ty, ty);
                state.prove_qualifiers(preds, &self.info);
            }
            PolyConstraintKind::Skolemize(ty, mono_tys, sigma) => {
                let forall = state.find_scheme(sigma).unwrap();
                self.info.skolemized_type_scheme(mono_tys, &forall);
                let (preds, skolem_ty) = state
                    .skolemize_faked(self.info.clone(), mono_tys.clone(), forall)
                    .split();

                self.info.equality_type_pair(ty, ty);
                state.assume_qualifiers(preds, &self.info);
                state.push_constraint(Constraint::from(EqualityConstraint::new(
                    ty.clone(),
                    skolem_ty,
                    self.info.clone(),
                )));
            }
            PolyConstraintKind::Implicit(lhs, mono_tys, rhs) => {
                let sigma_var = state.get_unique();
                let gen_constraint = PolymorphismConstraint {
                    kind: PolyConstraintKind::Generalize(sigma_var, mono_tys.clone(), rhs.clone()),
                    info: self.info.clone(),
                };
                let inst_constraint = PolymorphismConstraint {
                    kind: PolyConstraintKind::Instantiate(lhs.clone(), Sigma::Var(sigma_var)),
                    info: self.info.clone(),
                };

                state.push_constraints(vec![
                    Constraint::from(gen_constraint),
                    Constraint::from(inst_constraint),
                ]);
            }
        }
    }
}
