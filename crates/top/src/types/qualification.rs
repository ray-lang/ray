use crate::util::DisplayableVec;

use super::{HasTypes, ShowQuantors, Subst, Substitutable, Ty};

#[derive(Debug)]
pub struct Displayable<T>(T)
where
    T: std::fmt::Display;

impl<T> std::fmt::Display for Displayable<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<T> From<T> for Displayable<T>
where
    T: std::fmt::Display,
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
    T: std::fmt::Display,
{
    fn show_qualifiers(&self) -> Vec<String> {
        vec![self.to_string()]
    }
}

impl<T> ShowQualifiers for Vec<T>
where
    T: std::fmt::Display + ShowQualifiers,
{
    fn show_qualifiers(&self) -> Vec<String> {
        self.iter().flat_map(|v| v.show_qualifiers()).collect()
    }
}

#[derive(Debug, Clone)]
pub struct Qualification<P, T> {
    pub qualifiers: P,
    pub ty: T,
}

impl<P, T> std::fmt::Display for Qualification<P, T>
where
    P: std::fmt::Display + ShowQualifiers,
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.qualifiers.show_context())?;
        write!(f, "{}", self.ty)
    }
}

impl<P, T> Into<Qualification<DisplayableVec<P>, T>> for Qualification<Vec<P>, T>
where
    P: std::fmt::Display,
{
    fn into(self) -> Qualification<DisplayableVec<P>, T> {
        Qualification {
            qualifiers: self.qualifiers.into(),
            ty: self.ty,
        }
    }
}

impl<P, T> ShowQuantors for Qualification<P, T>
where
    P: std::fmt::Display + ShowQualifiers,
    T: std::fmt::Display,
{
}

impl<P, T> Substitutable for Qualification<P, T>
where
    P: Substitutable,
    T: Substitutable,
{
    fn apply_subst(&mut self, subst: &Subst) {
        self.qualifiers.apply_subst(subst);
        self.ty.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<u32> {
        self.qualifiers
            .free_vars()
            .into_iter()
            .chain(self.ty.free_vars())
            .collect()
    }
}

impl<P, T> HasTypes for Qualification<P, T>
where
    P: HasTypes,
    T: HasTypes,
{
    fn get_types(&self) -> Vec<&Ty> {
        self.qualifiers
            .get_types()
            .into_iter()
            .chain(self.ty.get_types())
            .collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ()) {
        self.qualifiers.change_types(f);
        self.ty.change_types(f);
    }
}

impl<P, T> Qualification<P, T> {
    pub fn new(qualifiers: P, ty: T) -> Self {
        Self { qualifiers, ty }
    }

    pub fn qualifiers(&self) -> &P {
        &self.qualifiers
    }

    pub fn ty(&self) -> &T {
        &self.ty
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
