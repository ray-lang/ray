use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    constraint::Constraint,
    directives::TypeClassDirective,
    types::{ClassEnv, OrderedTypeSynonyms, Scheme, Subst},
    ForAll, Predicates, Qualification, Substitutable, Ty, TyVar,
};

pub mod greedy;
mod info;

pub use info::*;

pub trait Solver<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn solve(
        self,
        options: SolveOptions<I, T, V>,
        constraints: Vec<Constraint<I, T, V>>,
    ) -> SolveResult<I, T, V>;
}

#[derive(Debug)]
pub struct SolveOptions<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub unique: u32,
    pub type_synonyms: OrderedTypeSynonyms<T, V>,
    pub class_env: ClassEnv<T, V>,
    pub type_class_directives: Vec<TypeClassDirective<I, T, V>>,
    pub stop_after_first_error: bool,
    pub check_conditions: bool,
    _phantom: PhantomData<V>,
}

impl<I, T, V> Default for SolveOptions<I, T, V>
where
    T: Ty<V> + Default,
    V: TyVar + Default,
{
    fn default() -> Self {
        Self {
            unique: 0,
            type_synonyms: Default::default(),
            class_env: Default::default(),
            type_class_directives: Default::default(),
            stop_after_first_error: Default::default(),
            check_conditions: Default::default(),
            _phantom: Default::default(),
        }
    }
}

#[derive(Debug, Default)]
pub struct SolveResult<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub unique: u32,
    pub subst: Subst<V, T>,
    pub type_schemes: Subst<V, Scheme<Predicates<T, V>, T, V>>,
    pub inst_type_schemes: Subst<V, Scheme<Predicates<T, V>, T, V>>,
    pub qualifiers: Predicates<T, V>,
    pub errors: Vec<(String, I)>,
    pub solved_constraints: Vec<Constraint<I, T, V>>,
}

impl<I, T, V> Display for SolveResult<I, T, V>
where
    I: Display,
    T: Display + Ty<V>,
    V: Display + Debug + TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SolveResult {{\n")?;
        write!(f, "  unique: {},\n", self.unique)?;

        write!(f, "  subst: ")?;
        if self.subst.is_empty() {
            write!(f, "{{}}")?;
        } else {
            write!(f, "{{\n")?;
            for (i, (var, ty)) in self.subst.iter().enumerate() {
                write!(f, "    {}: {}", var, ty)?;
                if i < self.subst.len() - 1 {
                    write!(f, ",\n")?;
                } else {
                    write!(f, "\n")?;
                }
            }
            write!(f, "  }},\n")?;
        }

        write!(f, "  type_schemes: ")?;
        if self.type_schemes.is_empty() {
            write!(f, "{{}}\n")?;
        } else {
            write!(f, "{{\n")?;
            for (var, scheme) in self.type_schemes.iter() {
                write!(f, "    {}: {}\n", var, scheme)?;
            }
            write!(f, "  }},\n")?;
        }

        write!(f, "  inst_type_schemes: ")?;
        if self.inst_type_schemes.is_empty() {
            write!(f, "{{}}\n")?;
        } else {
            write!(f, "{{\n")?;
            for (var, scheme) in self.inst_type_schemes.iter() {
                write!(f, "    {}: {}\n", var, scheme)?;
            }
            write!(f, "  }},\n")?;
        }

        if self.qualifiers.is_empty() {
            write!(f, "  qualifiers: [],\n")?;
        } else {
            write!(f, "  qualifiers: [\n")?;
            for pred in &self.qualifiers {
                write!(f, "    {}\n", pred)?;
            }
            write!(f, "  ],\n")?;
        }

        if self.solved_constraints.is_empty() {
            write!(f, "  solved_constraints: [],\n")?;
        } else {
            write!(f, "  solved_constraints: [\n")?;
            for (i, constraint) in self.solved_constraints.iter().enumerate() {
                write!(f, "    {}", constraint)?;
                if i < self.solved_constraints.len() - 1 {
                    write!(f, ",\n")?;
                } else {
                    write!(f, "\n")?;
                }
            }
            write!(f, "  ],\n")?;
        }

        if self.errors.is_empty() {
            write!(f, "  errors: [],\n")?;
        } else {
            write!(f, "  errors: [\n")?;
            for (i, (msg, info)) in self.errors.iter().enumerate() {
                write!(f, "    ({:?},\n", msg)?;
                let info = info.to_string();
                for line in info.split('\n') {
                    write!(f, "    {}\n", line)?
                }
                write!(f, ")")?;
                if i < self.errors.len() - 1 {
                    write!(f, ",\n")?;
                }
            }
            write!(f, "  ]\n")?;
        }

        write!(f, "}}")
    }
}

impl<I, T, V> SolveResult<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn scheme_subst(&self) -> Subst<V, Scheme<Predicates<T, V>, T, V>> {
        let mut subst = Subst::new();
        for (var, ty) in self.subst.iter() {
            let scheme = self.scheme_with_preds(ty);
            subst.insert(var.clone(), scheme);
        }
        subst
    }

    pub fn scheme_with_preds(&self, ty: &T) -> Scheme<Predicates<T, V>, T, V> {
        let mut vars = ty.free_vars().into_iter().cloned().collect::<Vec<_>>();
        vars.sort();
        vars.dedup();
        let mut preds = self
            .qualifiers
            .iter()
            .filter(|pred| pred.free_vars().iter().any(|var| vars.contains(var)))
            .cloned()
            .collect::<Vec<_>>();
        preds.sort();
        preds.dedup();
        ForAll::new(
            vars,
            Qualification::new(Predicates::from(preds), ty.clone()),
        )
    }
}
