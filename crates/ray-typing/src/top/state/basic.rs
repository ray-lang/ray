use crate::top::{
    Ty, TyVar,
    constraint::Constraint,
    interface::basic::{ErrorLabel, HasBasic},
    state::HasState,
};

#[derive(Debug, Default)]
pub struct BasicState<I, T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub(crate) constraints: Vec<Constraint<I, T, V>>,
    pub(crate) errors: Vec<(ErrorLabel, I)>,
    pub(crate) conditions: Vec<(String, bool)>,
    pub(crate) stop_after_first_error: bool,
    pub(crate) check_conditions: bool,
}

impl<I, S, T, V> HasBasic<I, T, V> for S
where
    I: 'static,
    S: HasState<BasicState<I, T, V>>,
    T: Ty<V> + 'static,
    V: TyVar + 'static,
{
    fn push_constraint(&mut self, constraint: Constraint<I, T, V>) {
        self.state_mut().constraints.push(constraint);
    }

    fn push_constraints(&mut self, constraints: Vec<Constraint<I, T, V>>) {
        self.state_mut().constraints.extend(constraints);
    }

    fn pop_constraint(&mut self) -> Option<Constraint<I, T, V>> {
        self.state_mut().constraints.pop()
    }

    fn discard_constraints(&mut self) {
        self.state_mut().constraints.clear();
    }

    fn add_labeled_err(&mut self, label: ErrorLabel, info: I) {
        let state = self.state_mut();
        state.errors.push((label, info));
        if state.stop_after_first_error {
            self.discard_constraints();
        }
    }

    fn get_labeled_errs(&self) -> &Vec<(ErrorLabel, I)> {
        &self.state().errors
    }

    fn update_err_info(&mut self, mut f: impl FnMut(&mut I)) {
        for (_, info) in &mut self.state_mut().errors {
            f(info);
        }
    }

    fn add_check(&mut self, label: &str, check: bool) {
        self.state_mut().conditions.push((label.to_string(), check));
    }

    fn get_checks(&self) -> &Vec<(String, bool)> {
        &self.state().conditions
    }

    fn stop_after_first_error(&self) -> bool {
        self.state().stop_after_first_error
    }

    fn set_stop_after_first_error(&mut self, stop: bool) {
        self.state_mut().stop_after_first_error = stop;
    }

    fn check_conditions(&self) -> bool {
        self.state().check_conditions
    }

    fn set_check_conditions(&mut self, check: bool) {
        self.state_mut().check_conditions = check;
    }
}
