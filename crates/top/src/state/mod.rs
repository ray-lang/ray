use std::{
    fmt::Display,
    ops::{Deref, DerefMut},
};

use crate::{
    TyVar,
    constraint::InfoDetail,
    interface::{
        basic::{ErrorLabel, HasBasic},
        subst::HasSubst,
        type_inference::{HasTypeInference, VarKind},
    },
    types::{Subst, Ty, mgu_with_synonyms},
};

mod basic;
mod overloading;

pub use basic::*;
pub use overloading::*;

pub trait HasState<T> {
    fn state(&self) -> &T;
    fn state_mut(&mut self) -> &mut T;
}

impl<A, I, T, V> HasSubst<I, T, V> for A
where
    A: HasState<SimpleState<T, V>> + HasBasic<I, T, V> + HasTypeInference<I, T, V>,
    I: Clone + InfoDetail,
    T: Display + Ty<V>,
    V: Display + TyVar + 'static,
{
    fn make_subst_consistent(&mut self) {
        // do nothing
    }

    fn unify_terms(&mut self, info: &I, lhs: &T, rhs: &T) {
        let synonyms = self.type_synonyms();
        let mut lhs = lhs.clone();
        lhs.apply_subst_from(self);
        let mut rhs = rhs.clone();
        rhs.apply_subst_from(self);

        log::debug!("[unify_terms] lhs={:?}, rhs={:?}", lhs, rhs);
        match mgu_with_synonyms(&lhs, &rhs, &Subst::new(), synonyms) {
            Ok((_, subst)) => {
                let mut filtered = Subst::new();

                for (var, ty) in subst.into_iter() {
                    // If the key is rigid but the value is a flexible var, flip the binding
                    // and *propagate rigidity* to the flexible var.
                    if self.is_rigid(&var) {
                        if let Some(other_var) = ty.maybe_var() {
                            // Same rigid var: no-op.
                            if &var == other_var {
                                continue;
                            }

                            // rigid := flexible_meta  → flip to flexible_meta := rigid
                            // and mark the flexible meta var as rigid so defaulting
                            // and later passes treat it as non-defaultable.
                            if !self.is_rigid(other_var) {
                                log::debug!(
                                    "[unify_terms]: setting other var {:?} to RIGID based on var {:?}",
                                    other_var,
                                    var
                                );
                                self.set_var_kind(other_var.clone(), VarKind::Rigid);
                                filtered.insert(other_var.clone(), T::var(var.clone()));
                                continue;
                            }

                            // rigid1 := rigid2 (different skolems / rigids).
                            // For now, treat as a no-op rather than an error.
                            continue;
                        }

                        // rigid := concrete type (not a var) is still an error.
                        let mut info = info.clone();
                        info.add_detail(&format!(
                            "cannot bind rigid type variable {} during unification",
                            var
                        ));
                        self.add_labeled_err(ErrorLabel::RigidTypeVariable, info);
                        return;
                    }

                    // Normal case: flexible := ty
                    filtered.insert(var, ty);
                }

                log::debug!(
                    "[unify_terms] union with global substitution: {:?}",
                    filtered
                );
                self.state_mut().union(filtered);
            }
            Err(err) => {
                let mut info = info.clone();
                info.add_detail(&err.to_string());
                self.add_labeled_err(ErrorLabel::Unification, info);
            }
        }
    }

    fn get_subst(&self) -> &Subst<V, T> {
        &self.state()
    }

    fn get_subst_mut(&mut self) -> &mut Subst<V, T> {
        self.state_mut().deref_mut()
    }

    fn find_subst_for_var(&self, var: &V) -> T {
        self.state().lookup_var(var)
    }
}

#[derive(Debug, Default, Clone)]
pub struct SimpleState<T, V>(Subst<V, T>)
where
    T: Ty<V>,
    V: TyVar;

impl<T, V> Deref for SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = Subst<V, T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, V> DerefMut for SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, V> SimpleState<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn to_subst(self) -> Subst<V, T> {
        self.0
    }
}
