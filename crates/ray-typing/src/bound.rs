pub trait GreatestLowerBound {
    fn greatest_lower_bound(&self, other: &Self) -> Self;
}

pub trait LeastUpperBound {
    fn least_upper_bound(&self, other: &Self) -> Self;
}
