// use std::{
//     fmt::Display,
//     hash::Hash,
//     ops::{Deref, DerefMut},
// };

// use crate::{
//     types::{ShowQualifiers, Subst, Substitutable},
//     Ty, TyVar,
// };

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
// pub struct DisplayableVec<'a, T>(&'a Vec<T>)
// where
//     T: Display;

// impl<'a, T> Deref for DisplayableVec<'a, T>
// where
//     T: Display,
// {
//     type Target = Vec<T>;

//     fn deref(&self) -> &Self::Target {
//         self.0
//     }
// }

// impl<'a, T> Display for DisplayableVec<'a, T>
// where
//     T: Display,
// {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "[")?;
//         for (i, x) in self.0.iter().enumerate() {
//             if i > 0 {
//                 write!(f, ", ")?;
//             }
//             write!(f, "{}", x)?;
//         }

//         write!(f, "]")
//     }
// }

// impl<'a, T> Into<Vec<T>> for DisplayableVec<'a, T>
// where
//     T: Display,
// {
//     fn into(self) -> Vec<T> {
//         self.0
//     }
// }

// impl<'a, T> From<&'a Vec<T>> for DisplayableVec<'a, T>
// where
//     T: Display,
// {
//     fn from(t: &'a Vec<T>) -> Self {
//         Self(t)
//     }
// }

// // impl<A, T, V> Substitutable<V, T> for DisplayableVec<A>
// // where
// //     A: Display + Substitutable<V, T>,
// //     T: Ty<V>,
// //     V: TyVar,
// // {
// //     fn apply_subst(&mut self, subst: &Subst<V, T>) {
// //         for x in &mut self.0 {
// //             x.apply_subst(subst);
// //         }
// //     }

// //     fn free_vars(&self) -> Vec<&V> {
// //         self.0.iter().flat_map(|x| x.free_vars()).collect()
// //     }
// // }

// impl<'a, T> ShowQualifiers for DisplayableVec<'a, T>
// where
//     T: Display + ShowQualifiers,
// {
//     fn show_qualifiers(&self) -> Vec<String> {
//         self.0.show_qualifiers()
//     }
// }
