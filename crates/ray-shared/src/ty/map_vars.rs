use std::collections::HashMap;

use crate::ty::{SchemaVarAllocator, Ty, TyVar};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MappingState {
    pub forward_map: HashMap<TyVar, TyVar>,
    pub reverse_map: HashMap<TyVar, TyVar>,
}

impl MappingState {
    fn get_var_mapping(&self, var: &TyVar) -> Option<&TyVar> {
        self.forward_map.get(var)
    }

    fn add_var_mapping(&mut self, var: &TyVar, mapped_var: &TyVar) {
        self.forward_map.insert(var.clone(), mapped_var.clone());
        self.reverse_map.insert(mapped_var.clone(), var.clone());
    }
}

pub trait MapVars: Sized {
    fn map_vars(
        &self,
        state: &MappingState,
        allocator: &mut SchemaVarAllocator,
    ) -> (Self, MappingState);
}

impl MapVars for Vec<Ty> {
    fn map_vars(
        &self,
        state: &MappingState,
        allocator: &mut SchemaVarAllocator,
    ) -> (Self, MappingState) {
        let mut out = self.clone();
        let mut state = state.clone();
        for ty in out.iter_mut() {
            let (mapped_ty, mapped_state) = ty.map_vars(&state, allocator);
            *ty = mapped_ty;
            state = mapped_state;
        }

        (out, state)
    }
}

impl MapVars for Ty {
    fn map_vars(
        &self,
        state: &MappingState,
        allocator: &mut SchemaVarAllocator,
    ) -> (Self, MappingState) {
        let mut mapped_ty = self.clone();
        let mut state = state.clone();
        match &mut mapped_ty {
            Ty::Never | Ty::Any | Ty::Const(_) => {}
            Ty::Var(tv) => {
                if tv.is_ret_placeholder() {
                    return (mapped_ty, state);
                }

                *tv = if let Some(mapped_tv) = state.get_var_mapping(&tv) {
                    log::debug!("found mapping: {} -> {}", tv, mapped_tv);
                    mapped_tv.clone()
                } else {
                    let mapped_tv = allocator.alloc();
                    state.add_var_mapping(tv, &mapped_tv);
                    mapped_tv
                }
            }
            Ty::Tuple(tys) => {
                let (new_tys, mapped_state) = tys.map_vars(&state, allocator);
                *tys = new_tys;
                state = mapped_state;
            }
            Ty::Proj(_, param_tys) => {
                let (new_tys, mapped_state) = param_tys.map_vars(&state, allocator);
                *param_tys = new_tys;
                state = mapped_state;
            }
            Ty::Array(inner, _)
            | Ty::Ref(inner)
            | Ty::MutRef(inner)
            | Ty::IdRef(inner)
            | Ty::RawPtr(inner) => {
                let (new_ty, mapped_state) = inner.map_vars(&state, allocator);
                **inner = new_ty;
                state = mapped_state;
            }
            Ty::Func(param_tys, ret_ty) => {
                let (new_tys, mapped_state) = param_tys.map_vars(&state, allocator);
                *param_tys = new_tys;
                state = mapped_state;

                let (new_ty, mapped_state) = ret_ty.map_vars(&state, allocator);
                **ret_ty = new_ty;
                state = mapped_state;
            }
        }

        (mapped_ty, state)
    }
}

#[cfg(test)]
mod tests {
    use crate::ty::{
        SchemaVarAllocator, Ty, TyVar,
        map_vars::{MapVars, MappingState},
    };

    #[test]
    fn maps_vars_for_var_new_var() {
        let var = TyVar::new("'a");
        let ty = Ty::Var(var.clone());
        let mut allocator = SchemaVarAllocator::new();
        let (mapped_ty, state) = ty.map_vars(&MappingState::default(), &mut allocator);

        let var_mapping = state.get_var_mapping(&var).cloned();
        assert!(var_mapping.is_some());
        let mapped_var = var_mapping.unwrap();
        assert_eq!(Ty::Var(mapped_var.clone()), mapped_ty);

        let reverse_mapping = state.reverse_map.get(&mapped_var).cloned();
        assert!(reverse_mapping.is_some());
        let original_var = reverse_mapping.unwrap();
        assert_eq!(var, original_var);
    }

    #[test]
    fn maps_var_for_var_existing_var() {
        let var = TyVar::new("'a");
        let ty = Ty::Var(var.clone());
        let mut allocator = SchemaVarAllocator::new();
        let mapped_var = allocator.alloc();
        let mut state = MappingState::default();
        state.add_var_mapping(&var, &mapped_var);

        let (mapped_ty, new_state) = ty.map_vars(&state, &mut allocator);

        let var_mapping = new_state.get_var_mapping(&var).cloned();
        assert!(var_mapping.is_some());
        let mapped_var = var_mapping.unwrap();
        assert_eq!(Ty::Var(mapped_var.clone()), mapped_ty);

        let reverse_mapping = new_state.reverse_map.get(&mapped_var).cloned();
        assert!(reverse_mapping.is_some());
        let original_var = reverse_mapping.unwrap();
        assert_eq!(var, original_var);

        assert_eq!(state, new_state);
    }

    #[test]
    fn maps_vars_in_mut_ref() {
        let var = TyVar::new("'a");
        let ty = Ty::mut_ref_of(Ty::Var(var.clone()));
        let mut allocator = SchemaVarAllocator::new();
        let (mapped_ty, state) = ty.map_vars(&MappingState::default(), &mut allocator);

        let mapped_var = state.get_var_mapping(&var).cloned().unwrap();
        assert_eq!(mapped_ty, Ty::mut_ref_of(Ty::Var(mapped_var)));
    }

    #[test]
    fn maps_vars_in_id_ref() {
        let var = TyVar::new("'a");
        let ty = Ty::id_ref_of(Ty::Var(var.clone()));
        let mut allocator = SchemaVarAllocator::new();
        let (mapped_ty, state) = ty.map_vars(&MappingState::default(), &mut allocator);

        let mapped_var = state.get_var_mapping(&var).cloned().unwrap();
        assert_eq!(mapped_ty, Ty::id_ref_of(Ty::Var(mapped_var)));
    }

    #[test]
    fn maps_vars_preserves_ref_kind() {
        let var = TyVar::new("'a");
        let mut allocator = SchemaVarAllocator::new();

        let shared = Ty::ref_of(Ty::Var(var.clone()));
        let (mapped_shared, _) = shared.map_vars(&MappingState::default(), &mut allocator);
        assert!(matches!(mapped_shared, Ty::Ref(_)));

        let mut_ref = Ty::mut_ref_of(Ty::Var(var.clone()));
        let (mapped_mut, _) = mut_ref.map_vars(&MappingState::default(), &mut allocator);
        assert!(matches!(mapped_mut, Ty::MutRef(_)));

        let id_ref = Ty::id_ref_of(Ty::Var(var.clone()));
        let (mapped_id, _) = id_ref.map_vars(&MappingState::default(), &mut allocator);
        assert!(matches!(mapped_id, Ty::IdRef(_)));
    }
}
