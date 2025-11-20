use std::{
    fmt::{Debug, Display},
    ops::{Deref, DerefMut},
    str::FromStr,
};

use crate::{
    InfoJoin, Substitutable, Ty, TyVar,
    constraint::{Constraint, InfoDetail, PolyTypeConstraintInfo, Solvable, TypeConstraintInfo},
    interface::{
        basic::HasBasic,
        qualification::HasQual,
        type_inference::{HasTypeInference, TypeInferState, VarKind},
    },
    state::{BasicState, HasState, OverloadingState, SimpleState},
};

use super::{SolveOptions, SolveResult, Solver};

#[derive(Debug, Default)]
pub struct GreedyState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    simple_state: SimpleState<T, V>,
    basic_state: BasicState<I, T, V>,
    infer_state: TypeInferState<I, T, V>,
    overloading_state: OverloadingState<I, T, V>,
}

impl<I, T, V> HasState<SimpleState<T, V>> for GreedyState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn state(&self) -> &SimpleState<T, V> {
        &self.simple_state
    }

    fn state_mut(&mut self) -> &mut SimpleState<T, V> {
        &mut self.simple_state
    }
}

impl<I, T, V> HasState<BasicState<I, T, V>> for GreedyState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn state(&self) -> &BasicState<I, T, V> {
        &self.basic_state
    }

    fn state_mut(&mut self) -> &mut BasicState<I, T, V> {
        &mut self.basic_state
    }
}

impl<I, T, V> HasState<TypeInferState<I, T, V>> for GreedyState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn state(&self) -> &TypeInferState<I, T, V> {
        &self.infer_state
    }

    fn state_mut(&mut self) -> &mut TypeInferState<I, T, V> {
        &mut self.infer_state
    }
}

impl<I, T, V> HasState<OverloadingState<I, T, V>> for GreedyState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn state(&self) -> &OverloadingState<I, T, V> {
        &self.overloading_state
    }

    fn state_mut(&mut self) -> &mut OverloadingState<I, T, V> {
        &mut self.overloading_state
    }
}

#[derive(Debug, Default)]
pub struct GreedySolver<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    state: GreedyState<I, T, V>,
}

impl<I, T, V> Deref for GreedySolver<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = GreedyState<I, T, V>;

    fn deref(&self) -> &Self::Target {
        &self.state
    }
}

impl<I, T, V> DerefMut for GreedySolver<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.state
    }
}

impl<I, T, V> HasState<GreedyState<I, T, V>> for GreedySolver<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn state(&self) -> &GreedyState<I, T, V> {
        &self.state
    }

    fn state_mut(&mut self) -> &mut GreedyState<I, T, V> {
        &mut self.state
    }
}

impl<I, T, V> Solver<I, T, V> for GreedySolver<I, T, V>
where
    I: Display
        + Debug
        + Clone
        + Default
        + InfoDetail
        + InfoJoin
        + TypeConstraintInfo<I, T, V>
        + PolyTypeConstraintInfo<I, T, V>
        + 'static,
    V: Display + Debug + Ord + TyVar + 'static,
    T: Display + Ty<V> + 'static,
    <V as FromStr>::Err: Debug,
{
    fn solve(
        mut self,
        options: SolveOptions<I, T, V>,
        mut constraints: Vec<Constraint<I, T, V>>,
    ) -> SolveResult<I, T, V> {
        let SolveOptions {
            unique,
            type_synonyms,
            class_env,
            type_class_directives,
            stop_after_first_error,
            check_conditions,
            ..
        } = options;
        self.set_unique(unique);
        self.mark_var_range(0, unique, VarKind::Flexible);
        self.type_synonyms_mut().extend(type_synonyms);
        self.class_env_mut().extend(class_env);
        self.directives_mut().extend(type_class_directives);
        self.set_stop_after_first_error(stop_after_first_error);
        self.set_check_conditions(check_conditions);

        // we add the constraints in reverse because we pop them off
        constraints.reverse();
        self.push_constraints(constraints);

        let mut solved = vec![];
        while let Some(mut constraint) = self.pop_constraint() {
            constraint.solve(&mut self.state);
            solved.push(constraint);
        }

        self.make_consistent();
        self.check_skolems();
        self.improve();
        self.defaults();
        self.fields();
        self.improve(); // we need to ANOTHER improve step after we defualt
        self.ambiguities();
        self.unsolved_predicates();

        let state = self.state;

        let orig_subst = state.simple_state.to_subst();
        let mut subst = orig_subst.clone();
        for (_, ty) in subst.iter_mut() {
            ty.apply_subst(&orig_subst);
        }

        let mut type_schemes = state.infer_state.type_schemes;
        for (_, scheme) in type_schemes.iter_mut() {
            scheme.apply_subst_all(&subst);
        }

        let mut inst_type_schemes = state.infer_state.inst_type_schemes;
        for (_, scheme) in inst_type_schemes.iter_mut() {
            scheme.apply_subst_all(&subst);
            log::debug!("inst_type_scheme: {:?}", scheme);
        }

        let qualifiers = state
            .overloading_state
            .predicate_map
            .into_iter()
            .map(|mut p| {
                p.apply_subst(&subst);
                p
            })
            .collect();

        let skolems = state.infer_state.skolems;
        let var_kinds = state.infer_state.var_kinds;
        log::debug!("[solve (POST)] variable kinds: {:?}", var_kinds);

        SolveResult {
            unique: state.infer_state.unique,
            subst,
            type_schemes,
            inst_type_schemes,
            qualifiers,
            skolems,
            errors: state.basic_state.errors,
            solved_constraints: solved,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Display;

    use crate::{
        Subst, Substitutable, TyVar,
        constraint::{Constraint, EqualityConstraint},
        interface::basic::ErrorLabel,
        solver::{SolveOptions, Solver, TopInfo},
        types::Ty,
    };

    use super::GreedySolver;

    macro_rules! constraint {
        ([$a:expr] == [$b:expr]) => {
            Constraint::Equality(EqualityConstraint::new($a, $b, TopInfo::default()))
        };
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum BasicTy {
        Var(u32),
        Const(String),
        Tuple(Vec<BasicTy>),
        App(Box<BasicTy>, Vec<BasicTy>),
    }

    impl Default for BasicTy {
        fn default() -> Self {
            BasicTy::Const("".to_string())
        }
    }

    impl Display for BasicTy {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                BasicTy::Var(id) => write!(f, "?{}", id),
                BasicTy::Const(s) => write!(f, "{}", s),
                BasicTy::Tuple(tys) => {
                    write!(
                        f,
                        "({})",
                        tys.iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
                BasicTy::App(a, b) => write!(
                    f,
                    "({} [{}])",
                    a,
                    b.iter()
                        .map(|t| t.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            }
        }
    }

    impl Substitutable<u32, BasicTy> for BasicTy {
        fn apply_subst(&mut self, subst: &Subst<u32, BasicTy>) {
            match self {
                BasicTy::Var(v) => {
                    if let Some(t) = subst.get(v) {
                        *self = t.clone();
                    }
                }
                BasicTy::Tuple(tys) => {
                    for ty in tys {
                        ty.apply_subst(subst);
                    }
                }
                BasicTy::App(a, b) => {
                    a.apply_subst(subst);
                    b.apply_subst(subst);
                }
                BasicTy::Const(_) => {}
            }
        }

        fn apply_subst_all(&mut self, subst: &Subst<u32, BasicTy>) {
            self.apply_subst(subst);
        }

        fn free_vars(&self) -> Vec<&u32> {
            match self {
                BasicTy::Var(v) => vec![v],
                BasicTy::Tuple(tys) => tys.iter().flat_map(|t| t.free_vars()).collect(),
                BasicTy::App(a, b) => a.free_vars().into_iter().chain(b.free_vars()).collect(),
                BasicTy::Const(_) => vec![],
            }
        }
    }

    impl Ty<u32> for BasicTy {
        fn new(name: &str) -> Self {
            BasicTy::Const(name.to_string())
        }

        fn var(v: u32) -> Self {
            BasicTy::Var(v)
        }

        fn app(lhs: Self, rhs: Self) -> Self {
            BasicTy::App(Box::new(lhs), vec![rhs])
        }

        fn tuple(tys: Vec<Self>) -> Self {
            BasicTy::Tuple(tys)
        }

        fn ptr(_: Self) -> Self {
            panic!("no pointer")
        }

        fn maybe_var(&self) -> Option<&u32> {
            if let BasicTy::Var(v) = self {
                Some(v)
            } else {
                None
            }
        }

        fn maybe_const(&self) -> Option<&str> {
            if let BasicTy::Const(s) = self {
                Some(s)
            } else {
                None
            }
        }

        fn maybe_app(&self) -> Option<(Self, Vec<Self>)> {
            if let BasicTy::App(lhs, rhs) = self {
                Some((*lhs.clone(), rhs.clone()))
            } else {
                None
            }
        }

        fn maybe_func(&self) -> Option<(&Vec<Self>, &Self)> {
            todo!()
        }

        fn maybe_tuple(&self) -> Option<&Vec<Self>> {
            None
        }

        fn maybe_union(&self) -> Option<&Vec<Self>> {
            None
        }

        fn maybe_ptr(&self) -> Option<&Self> {
            None
        }

        fn is_tyvar(&self) -> bool {
            todo!()
        }

        fn in_head_normal_form(&self) -> bool {
            todo!()
        }

        fn name(&self) -> &str {
            todo!()
        }

        fn variables(&self) -> Vec<&u32>
        where
            u32: Ord,
        {
            todo!()
        }

        fn constants(&self) -> Vec<String> {
            todo!()
        }

        fn eq_with_synonyms(
            &self,
            _: &Self,
            _: &crate::OrderedTypeSynonyms<Self, u32>,
        ) -> Option<Self> {
            todo!()
        }

        fn freeze_vars(&self) -> Self
        where
            u32: std::fmt::Display,
        {
            todo!()
        }

        fn unfreeze_vars(&self) -> Self
        where
            u32: std::str::FromStr,
            <u32 as std::str::FromStr>::Err: std::fmt::Debug,
        {
            todo!()
        }
    }

    impl TyVar for u32 {
        fn from_u32(u: u32) -> Self {
            u
        }

        fn get_u32(&self) -> Option<u32> {
            Some(*self)
        }
    }

    #[test]
    pub fn test_greedy_1() {
        let constraints = vec![
            // TVar 0 .==. (TVar 1 .->. TVar 1) $ "a"
            constraint!([BasicTy::var(0)] == [BasicTy::arrow(BasicTy::Var(1), BasicTy::Var(1))]),
            // TVar 0 .==. (TVar 2 .->. TVar 3) $ "b"
            constraint!([BasicTy::Var(0)] == [BasicTy::arrow(BasicTy::Var(2), BasicTy::Var(3))]),
            // TVar 2 .==. intType $ "c"
            constraint!([BasicTy::Var(2)] == [BasicTy::new("int")]),
            // TVar 3 .==. boolType $ "d"
            constraint!([BasicTy::Var(3)] == [BasicTy::new("bool")]),
        ];

        let mut options = SolveOptions::default();
        options.unique = 4;

        let solver = GreedySolver::default();
        let result = solver.solve(options, constraints);
        if let Some((label, err)) = result.errors.first() {
            assert_eq!(label, &ErrorLabel::Unification);
            assert_eq!(err.get("detail"), Some("constant mismatch: bool != int"));
        } else {
            panic!("no errors");
        }
    }
}
