pub trait SortByIndexSlice {
    fn sort_by_index_slice(&mut self, indices: Vec<usize>);
}

impl<T> SortByIndexSlice for Vec<T> {
    fn sort_by_index_slice(&mut self, indices: Vec<usize>) {
        let mut indices = indices;
        for i in 0..indices.len() {
            let j = indices[i];
            if i != j {
                indices.swap(i, j);
                self.swap(i, j);
            }
        }
    }
}
