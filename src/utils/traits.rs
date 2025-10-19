pub trait DrainInPlace<T> {
    fn drain_in_place<F>(&mut self, f: F)
    where
        F: Fn(&T) -> bool;
}

impl<T> DrainInPlace<T> for Vec<T> {
    fn drain_in_place<F>(&mut self, f: F)
    where
        F: Fn(&T) -> bool,
    {
        let mut index = 0;
        while index < self.len() {
            if f(&self[index]) {
                self.remove(index);
            } else {
                index += 1;
            }
        }
    }
}
