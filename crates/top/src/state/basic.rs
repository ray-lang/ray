use crate::{constraint::Constraint, interface::basic::HasBasic, state::HasState};

#[derive(Debug, Default)]
pub struct BasicState<T> {
    pub(crate) constraints: Vec<Constraint<T>>,
    pub(crate) errors: Vec<(String, T)>,
    pub(crate) conditions: Vec<(String, bool)>,
    pub(crate) stop_after_first_error: bool,
    pub(crate) check_conditions: bool,
}

impl<S, T> HasBasic<T> for S
where
    S: HasState<BasicState<T>>,
    T: 'static,
{
    fn push_constraint(&mut self, constraint: Constraint<T>) {
        self.state_mut().constraints.push(constraint);
    }

    fn push_constraints(&mut self, constraints: Vec<Constraint<T>>) {
        self.state_mut().constraints.extend(constraints);
    }

    fn pop_constraint(&mut self) -> Option<Constraint<T>> {
        self.state_mut().constraints.pop()
    }

    fn discard_constraints(&mut self) {
        self.state_mut().constraints.clear();
    }

    fn add_labeled_err(&mut self, label: &str, info: T) {
        let state = self.state_mut();
        state.errors.push((label.to_string(), info));
        if state.stop_after_first_error {
            self.discard_constraints();
        }
    }

    fn get_labeled_errs(&self) -> &Vec<(String, T)> {
        &self.state().errors
    }

    fn update_err_info(&mut self, mut f: impl FnMut(&mut T)) {
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
