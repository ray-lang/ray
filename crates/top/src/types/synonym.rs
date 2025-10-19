use std::{
    collections::HashMap,
    fmt::Debug,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::TyVar;

use super::Ty;

#[derive(Default)]
pub struct TypeSynonyms<T, V>(
    HashMap<String, (usize, Box<dyn Fn(Vec<T>) -> T>)>,
    PhantomData<V>,
)
where
    T: Ty<V>,
    V: TyVar;

impl<T, V> Debug for TypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeSynonyms(")?;
        for (i, (k, (v, _))) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{} = {{ arity = {} }}", k, v)?;
        }

        write!(f, ")")
    }
}

impl<T, V> Deref for TypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = HashMap<String, (usize, Box<dyn Fn(Vec<T>) -> T>)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T, V> DerefMut for TypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T, V> TypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new() -> Self {
        TypeSynonyms(HashMap::new(), PhantomData)
    }

    pub fn add(&mut self, name: String, arity: usize, f: Box<dyn Fn(Vec<T>) -> T>) {
        self.insert(name, (arity, f));
    }

    pub fn expand_type(&self, ty: T) -> T {
        let ty = self.expand_type_constructor(ty);
        let (ty, xs) = ty.left_spine();
        xs.into_iter().fold(ty.clone(), Ty::app)
    }

    pub fn expand_type_constructor(&self, ty: T) -> T {
        if let Some(ty) = self.expand_tc(ty.clone()) {
            self.expand_type_constructor(ty)
        } else {
            ty
        }
    }

    fn expand_tc(&self, ty: T) -> Option<T> {
        let (left, args) = ty.left_spine();
        left.maybe_const()
            .and_then(|name| self.get(name))
            .and_then(move |(arity, f)| {
                if args.len() == *arity {
                    Some(f(args))
                } else {
                    None
                }
            })
    }

    pub fn is_phantom_synonym(&self, name: &str) -> bool {
        match self.get(name) {
            Some((arity, f)) => {
                let is = (0..(*arity as u32)).collect::<Vec<_>>();
                let vars = is
                    .iter()
                    .map(|&i| Ty::var(V::from_u32(i)))
                    .collect::<Vec<_>>();
                let ty = f(vars);
                let free_vars = ty.free_vars();
                is.iter().any(|i| !free_vars.contains(&&V::from_u32(*i)))
            }
            None => false,
        }
    }
}

pub type TypeSynonymOrdering = HashMap<String, usize>;

#[derive(Debug, Default)]
pub struct OrderedTypeSynonyms<T, V>(TypeSynonymOrdering, TypeSynonyms<T, V>, PhantomData<V>)
where
    T: Ty<V>,
    V: TyVar;

impl<T, V> Deref for OrderedTypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Target = TypeSynonyms<T, V>;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl<T, V> DerefMut for OrderedTypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.1
    }
}

impl<T, V> Extend<(String, usize, usize, Box<dyn Fn(Vec<T>) -> T>)> for OrderedTypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar + 'static,
{
    fn extend<I: IntoIterator<Item = (String, usize, usize, Box<dyn Fn(Vec<T>) -> T>)>>(
        &mut self,
        iter: I,
    ) {
        for (name, arity, order, f) in iter {
            self.insert(name, order, arity, f);
        }
    }
}

impl<T, V> IntoIterator for OrderedTypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    type Item = (String, usize, usize, Box<dyn Fn(Vec<T>) -> T>);
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(mut self) -> Self::IntoIter {
        self.0
            .into_iter()
            .map(|(name, ord)| {
                let (arity, f) = self.1.remove(&name).unwrap();
                (name, ord, arity, f)
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl<T, V> OrderedTypeSynonyms<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    pub fn new() -> Self {
        OrderedTypeSynonyms(HashMap::new(), TypeSynonyms::new(), PhantomData)
    }

    pub fn insert(
        &mut self,
        name: String,
        order: usize,
        arity: usize,
        f: Box<dyn Fn(Vec<T>) -> T>,
    ) {
        self.0.insert(name.clone(), order);
        self.1.add(name, arity, f);
    }

    pub fn order(&self, name: &str) -> Option<usize> {
        self.0.get(name).cloned()
    }

    pub fn expand_ordered(&self, a: T, b: T) -> Option<(T, T)> {
        let f = |ty: T| {
            let (ty, _) = ty.left_spine();
            if let Some(name) = ty.maybe_const() {
                self.order(name)
            } else {
                None
            }
        };

        match (f(a.clone()), f(b.clone())) {
            (Some(i), Some(j)) if i > j => self.expand_tc(b).map(|b| (a, b)),
            (Some(_), _) => self.expand_tc(a).map(|a| (a, b)),
            (_, Some(_)) => self.expand_tc(b).map(|b| (a, b)),
            _ => None,
        }
    }
}
