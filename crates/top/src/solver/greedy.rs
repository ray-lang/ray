use std::ops::{Deref, DerefMut};

use crate::{
    constraint::{Constraint, InfoDetail, PolyTypeConstraintInfo, Solvable, TypeConstraintInfo},
    interface::{
        basic::HasBasic,
        qualification::HasQual,
        type_inference::{HasTypeInference, TypeInferState},
    },
    state::{BasicState, HasState, OverloadingState, SimpleState},
};

use super::{SolveOptions, SolveResult, Solver};

#[derive(Debug, Default)]
pub struct GreedyState<T> {
    simple_state: SimpleState,
    basic_state: BasicState<T>,
    infer_state: TypeInferState<T>,
    overloading_state: OverloadingState<T>,
}

impl<T> HasState<SimpleState> for GreedyState<T> {
    fn state(&self) -> &SimpleState {
        &self.simple_state
    }

    fn state_mut(&mut self) -> &mut SimpleState {
        &mut self.simple_state
    }
}

impl<T> HasState<BasicState<T>> for GreedyState<T> {
    fn state(&self) -> &BasicState<T> {
        &self.basic_state
    }

    fn state_mut(&mut self) -> &mut BasicState<T> {
        &mut self.basic_state
    }
}

impl<T> HasState<TypeInferState<T>> for GreedyState<T> {
    fn state(&self) -> &TypeInferState<T> {
        &self.infer_state
    }

    fn state_mut(&mut self) -> &mut TypeInferState<T> {
        &mut self.infer_state
    }
}

impl<T> HasState<OverloadingState<T>> for GreedyState<T> {
    fn state(&self) -> &OverloadingState<T> {
        &self.overloading_state
    }

    fn state_mut(&mut self) -> &mut OverloadingState<T> {
        &mut self.overloading_state
    }
}

#[derive(Debug, Default)]
pub struct GreedySolver<T> {
    state: GreedyState<T>,
}

impl<T> Deref for GreedySolver<T> {
    type Target = GreedyState<T>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl<T> DerefMut for GreedySolver<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.state
    }
}

impl<T> HasState<GreedyState<T>> for GreedySolver<T> {
    fn state(&self) -> &GreedyState<T> {
        &self.state
    }

    fn state_mut(&mut self) -> &mut GreedyState<T> {
        &mut self.state
    }
}

impl<T> Solver<T> for GreedySolver<T>
where
    T: std::fmt::Display
        + Clone
        + Default
        + InfoDetail
        + TypeConstraintInfo<T>
        + PolyTypeConstraintInfo<T>
        + 'static,
{
    fn solve(
        mut self,
        options: SolveOptions<T>,
        constraints: Vec<Constraint<T>>,
    ) -> SolveResult<T> {
        let SolveOptions {
            unique,
            type_synonyms,
            class_env,
            type_class_directives,
            stop_after_first_error,
            check_conditions,
        } = options;
        self.set_unique(unique);
        self.type_synonyms_mut().extend(type_synonyms);
        self.class_env_mut().extend(class_env);
        self.directives_mut().extend(type_class_directives);
        self.set_stop_after_first_error(stop_after_first_error);
        self.set_check_conditions(check_conditions);

        self.push_constraints(constraints);

        while let Some(mut constraint) = self.pop_constraint() {
            constraint.solve(&mut self.state);
        }

        self.make_consistent();
        self.check_skolems();
        self.ambiguities();

        let state = self.state;

        SolveResult::new(
            state.infer_state.unique,
            state.simple_state.to_subst(),
            state.infer_state.type_schemes,
            state
                .overloading_state
                .predicate_map
                .qualifiers
                .into_iter()
                .map(|(p, _)| p)
                .collect(),
            state.basic_state.errors,
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        constraint::{Constraint, EqualityConstraint},
        solver::{SolveOptions, Solver, TopInfo},
        types::Ty,
    };

    use super::GreedySolver;

    macro_rules! constraint {
        ([$a:expr] == [$b:expr]) => {
            Constraint::Equality(EqualityConstraint::new($a, $b, TopInfo::default()))
        };
    }

    #[test]
    pub fn test_greedy_1() {
        let constraints = vec![
            // TVar 0 .==. (TVar 1 .->. TVar 1) $ "a"
            constraint!([Ty::Var(0)] == [Ty::arrow(Ty::Var(1), Ty::Var(1))]),
            // TVar 0 .==. (TVar 2 .->. TVar 3) $ "b"
            constraint!([Ty::Var(0)] == [Ty::arrow(Ty::Var(2), Ty::Var(3))]),
            // TVar 2 .==. intType $ "c"
            constraint!([Ty::Var(2)] == [Ty::new("int")]),
            // TVar 3 .==. boolType $ "d"
            constraint!([Ty::Var(3)] == [Ty::new("bool")]),
        ];

        let mut options = SolveOptions::default();
        options.unique = 4;

        let solver = GreedySolver::default();
        let result = solver.solve(options, constraints);
        if let Some((label, err)) = result.errors.first() {
            assert_eq!(label, "unification");
            assert_eq!(err.get("detail"), Some("constant mismatch: bool != int"));
        } else {
            panic!("no errors");
        }
    }
}
