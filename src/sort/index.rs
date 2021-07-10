pub trait SortByIndexSlice {
    fn sort_by_index_slice(&mut self, indices: Vec<usize>);
}

impl<T> SortByIndexSlice for Vec<T> {
    fn sort_by_index_slice(&mut self, mut indices: Vec<usize>) {
        for i in 0..indices.len() {
            let j = indices[i];
            if i != j {
                self.swap(i, j);
                for k in (i + 1)..indices.len() {
                    if i == indices[k] {
                        indices.swap(i, k);
                        break;
                    }
                }
            }
        }
    }
}
