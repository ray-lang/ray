mod predicates;
mod primitive;
mod qualification;
mod quantification;
mod schemes;
mod subst;
mod synonym;
mod unification;

pub use predicates::*;
pub use primitive::*;
pub use qualification::*;
pub use quantification::*;
pub use schemes::*;
pub use subst::*;
pub use synonym::*;
pub use unification::*;

pub trait HasTypes<T, V>
where
    T: Ty<V>,
    V: TyVar,
{
    fn get_types(&self) -> Vec<&T>;
    fn change_types(&mut self, f: &impl FnMut(&mut T) -> ());
}

impl<A, T, V> HasTypes<T, V> for Vec<A>
where
    A: HasTypes<T, V>,
    T: Ty<V>,
    V: TyVar,
{
    fn get_types(&self) -> Vec<&T> {
        self.iter().flat_map(|ty| ty.get_types()).collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut T) -> ()) {
        for ty in self.iter_mut() {
            ty.change_types(f);
        }
    }
}

impl<A, B, T, V> HasTypes<T, V> for (A, B)
where
    A: HasTypes<T, V>,
    B: HasTypes<T, V>,
    T: Ty<V>,
    V: TyVar,
{
    fn get_types(&self) -> Vec<&T> {
        self.0
            .get_types()
            .into_iter()
            .chain(self.1.get_types())
            .collect()
    }

    fn change_types(&mut self, f: &impl FnMut(&mut T) -> ()) {
        self.0.change_types(f);
        self.1.change_types(f);
    }
}

impl<A, T, V> HasTypes<T, V> for Option<A>
where
    A: HasTypes<T, V>,
    T: Ty<V>,
    V: TyVar,
{
    fn get_types(&self) -> Vec<&T> {
        match self {
            Some(ty) => ty.get_types(),
            None => vec![],
        }
    }

    fn change_types(&mut self, f: &impl FnMut(&mut T) -> ()) {
        if let Some(ty) = self {
            ty.change_types(f);
        }
    }
}

pub fn all_type_variables<'a, A, T, V>(value: &'a A) -> Vec<&'a V>
where
    A: HasTypes<T, V> + Substitutable<V, T>,
    T: Ty<V> + 'a,
    V: TyVar,
{
    value
        .get_types()
        .into_iter()
        .flat_map(|ty| ty.free_vars())
        .collect()
}

pub fn all_type_constants<A, T, V>(value: &A) -> Vec<String>
where
    A: HasTypes<T, V> + Substitutable<V, T>,
    T: Ty<V>,
    V: TyVar,
{
    value
        .get_types()
        .into_iter()
        .flat_map(|ty| ty.constants())
        .collect()
}
