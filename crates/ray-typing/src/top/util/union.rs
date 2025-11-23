pub trait Union {
    type Item;

    fn union<'a, T>(&'a self, other: T) -> UnionIter<'a, Self::Item>;
}

pub struct UnionIter<'a, Item> {
    iter: &'a mut dyn Iterator<Item = Item>,
}

impl Iterator for UnionIter<'_, ()> {
    type Item = ();

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}
