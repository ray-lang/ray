use crate::typing::top::solvers::Solution;

pub trait FormalizeTypes {
    fn formalize(self, solution: &mut Solution) -> Self;
}

impl<T> FormalizeTypes for Vec<T>
where
    T: FormalizeTypes,
{
    fn formalize(self, solution: &mut Solution) -> Self {
        self.into_iter().map(|t| t.formalize(solution)).collect()
    }
}

impl<T> FormalizeTypes for Box<T>
where
    T: FormalizeTypes,
{
    fn formalize(self, solution: &mut Solution) -> Self {
        Box::new((*self).formalize(solution))
    }
}
