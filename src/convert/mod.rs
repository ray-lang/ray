use std::collections::{HashMap, HashSet};

pub trait ToSet {
    type Item;
    fn to_set(self) -> HashSet<Self::Item>;
}

impl<I> ToSet for I
where
    I: IntoIterator,
    I::Item: std::cmp::Eq + std::hash::Hash,
{
    type Item = I::Item;

    fn to_set(self) -> HashSet<Self::Item> {
        self.into_iter().collect()
    }
}
