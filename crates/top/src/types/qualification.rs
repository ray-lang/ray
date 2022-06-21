use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::TyVar;

use super::{HasTypes, ShowQuantors, Subst, Substitutable, Ty};

#[derive(Debug)]
pub struct Displayable<T>(T)
where
    T: Display;

impl<T> Display for Displayable<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> From<T> for Displayable<T>
where
    T: Display,
{
    fn from(t: T) -> Self {
        Self(t)
    }
}

pub trait ShowQualifiers {
    fn show_qualifiers(&self) -> Vec<String>;

    fn show_context(&self) -> String {
        let qualifiers = self.show_qualifiers();
        match &qualifiers[..] {
            [] => "".to_string(),
            [x] => format!("{} => ", x),
            xs => format!("({}) => ", xs.join(", ")),
        }
    }
}

impl<T> ShowQualifiers for Displayable<T>
where
    T: Display,
{
    fn show_qualifiers(&self) -> Vec<String> {
        vec![self.to_string()]
    }
}

impl<T> ShowQualifiers for Vec<T>
where
    T: Display + ShowQualifiers,
{
    fn show_qualifiers(&self) -> Vec<String> {
        self.iter().flat_map(|v| v.show_qualifiers()).collect()
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Qualification<P, T> {
    pub qualifiers: P,
    pub ty: T,
}

impl<P, T> Display for Qualification<P, T>
where
    P: Display + ShowQualifiers,
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.qualifiers.show_context())?;
        write!(f, "{}", self.ty)
    }
}

impl<Q, P> ShowQuantors for Qualification<Q, P>
where
    Q: Display + ShowQualifiers,
    P: Display,
{
}

impl<Q, P, T, V> Substitutable<V, T> for Qualification<Q, P>
where
    Q: Substitutable<V, T>,
    P: Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    fn apply_subst(&mut self, subst: &Subst<V, T>) {
        self.qualifiers.apply_subst(subst);
        self.ty.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<&V> {
        self.qualifiers
            .free_vars()
            .into_iter()
            .chain(self.ty.free_vars())
            .collect()
    }
}

impl<Q, P, T, V> HasTypes<T, V> for Qualification<Q, P>
where
    Q: HasTypes<T, V>,
    P: HasTypes<T, V>,
    T: Ty<V>,
    V: TyVar,
{
    fn get_types(&self) -> Vec<&T> {
        self.qualifiers
            .get_types()
            .into_iter()
            .chain(self.ty.get_types())
            .collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut T) -> ()) {
        self.qualifiers.change_types(f);
        self.ty.change_types(f);
    }
}

impl<P, T> Qualification<P, T> {
    pub fn new(qualifiers: P, ty: T) -> Self {
        Self { qualifiers, ty }
    }

    pub fn unqualified(ty: T) -> Self
    where
        P: Default,
    {
        Self::new(P::default(), ty)
    }

    pub fn qualifiers(&self) -> &P {
        &self.qualifiers
    }

    pub fn qualifiers_mut(&mut self) -> &mut P {
        &mut self.qualifiers
    }

    pub fn ty(&self) -> &T {
        &self.ty
    }
    pub fn ty_mut(&mut self) -> &mut T {
        &mut self.ty
    }

    pub fn unqualify(self) -> T {
        self.ty
    }

    pub fn split(self) -> (P, T) {
        (self.qualifiers, self.ty)
    }
}

// impl<P, Q, T> Qualification<P, T>
// where
//     P: Substitutable + IntoIterator<Item = Q>,
//     Q: Substitutable,
//     T: Substitutable,
// {
//     pub fn qualify<Ctx>(ctx: Ctx, qualifiers: P, ty: T) -> Qualification<Vec<Q>, T>
//     where
//         Ctx: Substitutable,
//     {
//         let ctx_freevars = ctx.free_vars();
//         let freevars = ty.free_vars();
//         let vars = freevars
//             .iter()
//             .filter(|var| !ctx_freevars.contains(var))
//             .collect::<Vec<_>>();
//         let qualifiers = qualifiers
//             .into_iter()
//             .filter(|q| {
//                 let q_freevars = q.free_vars();
//                 vars.iter().all(|var| !q_freevars.contains(var))
//             })
//             .collect::<Vec<_>>();
//         Qualification { qualifiers, ty }
//     }
// }
