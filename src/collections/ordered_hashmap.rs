// use std::{
//     collections::HashMap,
//     iter::FromIterator,
//     ops::{Deref, DerefMut},
// };

// pub struct OrderedHashMap<K, V> {
//     order: Vec<K>,
//     keys: HashMap<K, usize>,
//     values: HashMap<usize, V>,
// }

// pub struct IntoIter<K, V> {
//     idx: usize,
//     map: OrderedHashMap<K, V>,
// }

// pub struct Iter<'a, K: 'a, V: 'a> {
//     idx: usize,
//     map: &'a OrderedHashMap<K, V>,
// }

// pub struct OrderedValues<'a, K: 'a, V: 'a> {
//     inner: Iter<'a, K, V>,
// }

// // impl<'a, K, V> Deref for OrderedHashMap<'a, K, V> {
// //     type Target = HashMap<K, V>;

// //     fn deref(&self) -> &Self::Target {
// //         &self.map
// //     }
// // }

// // impl<'a, K, V> DerefMut for OrderedHashMap<'a, K, V> {
// //     fn deref_mut(&mut self) -> &mut Self::Target {
// //         &mut self.map
// //     }
// // }

// impl<K, V> OrderedHashMap<K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     pub fn new() -> OrderedHashMap<K, V> {
//         OrderedHashMap {
//             order: Vec::new(),
//             keys: HashMap::new(),
//             values: HashMap::new(),
//         }
//     }

//     pub fn get(&self, k: &K) -> Option<&V> {
//         if let Some(idx) = self.keys.get(&k) {
//             self.values.get(idx)
//         } else {
//             None
//         }
//     }

//     pub fn iter(&self) -> Iter<'_, K, V> {
//         Iter::new(self)
//     }

//     pub fn values(&self) -> OrderedValues<'_, K, V> {
//         OrderedValues { inner: self.iter() }
//     }

//     pub fn insert(&mut self, k: K, v: V) {
//         let idx = self.order.len();
//         self.order.push(k.clone());
//         self.keys.insert(k, idx);
//         self.values.insert(idx, v);
//     }
// }

// impl<'a, K, V> IntoIterator for OrderedHashMap<'a, K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     type Item = (K, V);
//     type IntoIter = IntoIter<'a, K, V>;

//     fn into_iter(self) -> Self::IntoIter {
//         todo!()
//     }
// }

// impl<'a, K, V: 'a> FromIterator<(K, V)> for OrderedHashMap<'a, K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     fn from_iter<T>(iter: T) -> Self
//     where
//         T: IntoIterator<Item = (K, V)>,
//     {
//         let mut m = OrderedHashMap::new();
//         for (k, v) in iter {
//             m.insert(k, v);
//         }
//         m
//     }
// }

// impl<'a, K, V> Iterator for Iter<'a, K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     type Item = (&'a K, &'a V);

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.idx < self.map.order.len() {
//             let k = &self.map.order[self.idx];
//             let v = self.map.values.get(&self.idx).unwrap();
//             self.idx += 1;
//             Some((k, v))
//         } else {
//             None
//         }
//     }
// }

// impl<'a, K, V> Iter<'a, K, V> {
//     pub fn new(map: &'a OrderedHashMap<K, V>) -> Iter<'a, K, V> {
//         Iter { idx: 0, map }
//     }
// }

// impl<'a, K, V> Iterator for IntoIter<'a, K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     type Item = (K, V);

//     fn next(&mut self) -> Option<Self::Item> {
//         if self.idx < self.map.order.len() {
//             let k = self.map.order[self.idx];
//             let v = self.map.values[&self.idx];
//             self.idx += 1;
//             Some((k, v))
//         } else {
//             None
//         }
//     }
// }

// impl<'a, K, V> Iterator for OrderedValues<'a, K, V>
// where
//     K: Clone + std::hash::Hash + std::cmp::Eq,
// {
//     type Item = &'a V;

//     fn next(&mut self) -> Option<Self::Item> {
//         match self.inner.next() {
//             Some((_, v)) => Some(v),
//             _ => None,
//         }
//     }
// }
