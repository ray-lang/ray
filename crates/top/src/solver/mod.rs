use std::collections::HashMap;

use crate::{
    constraint::Constraint,
    directives::TypeClassDirective,
    types::{ClassEnv, OrderedTypeSynonyms, Predicate, Scheme, Subst},
};

pub mod greedy;
mod info;

pub use info::*;

pub trait Solver<T> {
    fn solve(self, options: SolveOptions<T>, constraints: Vec<Constraint<T>>) -> SolveResult<T>;
}

#[derive(Debug)]
pub struct SolveOptions<T> {
    unique: u32,
    type_synonyms: OrderedTypeSynonyms,
    class_env: ClassEnv,
    type_class_directives: Vec<TypeClassDirective<T>>,
    stop_after_first_error: bool,
    check_conditions: bool,
}

impl<T> Default for SolveOptions<T> {
    fn default() -> Self {
        Self {
            unique: 0,
            type_synonyms: Default::default(),
            class_env: Default::default(),
            type_class_directives: Default::default(),
            stop_after_first_error: Default::default(),
            check_conditions: Default::default(),
        }
    }
}

#[derive(Debug, Default)]
pub struct SolveResult<T> {
    pub unique: u32,
    pub subst: Subst,
    pub type_schemes: HashMap<u32, Scheme<Vec<Predicate>>>,
    pub qualifiers: Vec<Predicate>,
    pub errors: Vec<(String, T)>,
}

impl<T> SolveResult<T> {
    pub fn new(
        unique: u32,
        subst: Subst,
        type_schemes: HashMap<u32, Scheme<Vec<Predicate>>>,
        qualifiers: Vec<Predicate>,
        errors: Vec<(String, T)>,
    ) -> Self {
        Self {
            unique,
            subst,
            type_schemes,
            qualifiers,
            errors,
        }
    }
}
