use std::{
    cell::{Ref, RefCell, RefMut},
    ops::Deref,
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HashCell<T>
where
    T: std::hash::Hash,
{
    inner: RefCell<T>,
}

impl<T> std::fmt::Debug for HashCell<T>
where
    T: std::hash::Hash + std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.inner.borrow(), f)
    }
}

impl<T> std::fmt::Display for HashCell<T>
where
    T: std::hash::Hash + std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.inner.borrow(), f)
    }
}

impl<T> std::hash::Hash for HashCell<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.inner.borrow().hash(state);
    }
}

impl<T> HashCell<T>
where
    T: std::hash::Hash,
{
    pub fn new(value: T) -> HashCell<T> {
        HashCell {
            inner: RefCell::new(value),
        }
    }

    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        self.inner.borrow()
    }

    pub fn borrow_mut(&mut self) -> RefMut<'_, T> {
        self.inner.borrow_mut()
    }
}
