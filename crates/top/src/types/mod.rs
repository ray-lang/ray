mod classes;
mod primitive;
mod qualification;
mod quantification;
mod schemes;
mod subst;
mod synonym;
mod unification;

pub use classes::*;
pub use primitive::*;
pub use qualification::*;
pub use quantification::*;
pub use schemes::*;
pub use subst::*;
pub use synonym::*;
pub use unification::*;

pub trait HasTypes {
    fn get_types(&self) -> Vec<&Ty>;
    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ());
}

impl<T> HasTypes for Vec<T>
where
    T: HasTypes,
{
    fn get_types(&self) -> Vec<&Ty> {
        self.iter().flat_map(|ty| ty.get_types()).collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ()) {
        for ty in self.iter_mut() {
            ty.change_types(f);
        }
    }
}

impl<T, U> HasTypes for (T, U)
where
    T: HasTypes,
    U: HasTypes,
{
    fn get_types(&self) -> Vec<&Ty> {
        self.0
            .get_types()
            .into_iter()
            .chain(self.1.get_types())
            .collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ()) {
        self.0.change_types(f);
        self.1.change_types(f);
    }
}

impl<T> HasTypes for Option<T>
where
    T: HasTypes,
{
    fn get_types(&self) -> Vec<&Ty> {
        match self {
            Some(ty) => ty.get_types(),
            None => vec![],
        }
    }

    fn change_types(&mut self, f: &impl FnMut(&mut Ty) -> ()) {
        if let Some(ty) = self {
            ty.change_types(f);
        }
    }
}

pub fn all_type_variables<T>(value: &T) -> Vec<u32>
where
    T: HasTypes + Substitutable,
{
    value
        .get_types()
        .into_iter()
        .flat_map(|ty| ty.free_vars())
        .collect()
}

pub fn all_type_constants<T>(value: &T) -> Vec<String>
where
    T: HasTypes + Substitutable,
{
    value
        .get_types()
        .into_iter()
        .flat_map(|ty| ty.constants())
        .collect()
}
