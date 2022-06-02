use std::ops::{Deref, DerefMut};

use crate::{
    constraint::InfoDetail,
    interface::{basic::HasBasic, subst::HasSubst, type_inference::HasTypeInference},
    types::{mgu_with_synonyms, Subst, Substitutable, Ty},
};

mod basic;
mod overloading;

pub use basic::*;
pub use overloading::*;

pub trait HasState<T> {
    fn state(&self) -> &T;
    fn state_mut(&mut self) -> &mut T;
}

impl<A, T> HasSubst<T> for A
where
    A: HasState<SimpleState> + HasBasic<T> + HasTypeInference<T>,
    T: Clone + InfoDetail,
{
    fn make_subst_consistent(&mut self) {
        // do nothing
    }

    fn unify_terms(&mut self, info: &T, lhs: &Ty, rhs: &Ty) {
        let synonyms = self.type_synonyms();
        let mut lhs = lhs.clone();
        lhs.apply_subst_from(self);
        let mut rhs = rhs.clone();
        rhs.apply_subst_from(self);
        match mgu_with_synonyms(&lhs, &rhs, &Subst::new(), synonyms) {
            Ok((_, subst)) => {
                self.state_mut().extend(subst);
            }
            Err(err) => {
                let mut info = info.clone();
                info.add_detail(&err.to_string());
                self.add_labeled_err("unification", info)
            }
        }
    }

    fn get_subst(&self) -> &Subst {
        &self.state()
    }

    fn get_subst_mut(&mut self) -> &mut Subst {
        self.state_mut().deref_mut()
    }

    fn find_subst_for_var(&self, var: u32) -> Option<&Ty> {
        self.state().get(&var)
    }
}

#[derive(Debug, Default, Clone)]
pub struct SimpleState(Subst);

impl Deref for SimpleState {
    type Target = Subst;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SimpleState {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl SimpleState {
    pub fn to_subst(self) -> Subst {
        self.0
    }
}
