use std::collections::HashMap;

use ray_shared::{
    def::DefId, local_binding::LocalBindingId, node_id::NodeId, pathlib::ItemPath,
    resolution::DefTarget, ty::Ty,
};

use crate::{
    env::TypecheckEnv,
    types::{ImplKind, ImplTy, StructTy, TraitTy, TyScheme},
};

#[derive(Default)]
pub struct MockTypecheckEnv {
    pub structs: HashMap<ItemPath, StructTy>,
    pub traits: HashMap<ItemPath, TraitTy>,
    pub impls: Vec<ImplTy>,
    pub external_schemes: HashMap<DefId, TyScheme>,
}

impl MockTypecheckEnv {
    pub fn new() -> MockTypecheckEnv {
        MockTypecheckEnv::default()
    }

    pub fn add_struct(&mut self, path: ItemPath, struct_ty: StructTy) {
        self.structs.insert(path, struct_ty);
    }

    pub fn add_trait(&mut self, path: ItemPath, trait_ty: TraitTy) {
        self.traits.insert(path, trait_ty);
    }

    pub fn add_impl(&mut self, impl_ty: ImplTy) {
        self.impls.push(impl_ty);
    }

    pub fn add_external_scheme(&mut self, def_id: DefId, scheme: TyScheme) {
        self.external_schemes.insert(def_id, scheme);
    }
}

impl TypecheckEnv for MockTypecheckEnv {
    fn struct_def(&self, path: &ItemPath) -> Option<StructTy> {
        self.structs.get(path).cloned()
    }

    fn trait_def(&self, path: &ItemPath) -> Option<TraitTy> {
        self.traits.get(path).cloned()
    }

    fn all_traits(&self) -> Vec<TraitTy> {
        self.traits.values().cloned().collect()
    }

    fn impls_for_trait(&self, trait_path: &ItemPath) -> Vec<ImplTy> {
        self.impls
            .iter()
            .filter(|impl_ty| match &impl_ty.kind {
                ImplKind::Trait { trait_ty, .. } => trait_ty
                    .item_path()
                    .map(|p| p == trait_path)
                    .unwrap_or(false),
                ImplKind::Inherent { .. } => false,
            })
            .cloned()
            .collect()
    }

    fn inherent_impls(&self, type_path: &ItemPath) -> Vec<ImplTy> {
        self.impls
            .iter()
            .filter(|impl_ty| match &impl_ty.kind {
                ImplKind::Inherent { recv_ty } => {
                    recv_ty.item_path().map(|p| p == type_path).unwrap_or(false)
                }
                ImplKind::Trait { .. } => false,
            })
            .cloned()
            .collect()
    }

    fn impls_for_recv(&self, recv_path: &ItemPath) -> Vec<ImplTy> {
        self.impls
            .iter()
            .filter(|impl_ty| match &impl_ty.kind {
                ImplKind::Inherent { recv_ty } => {
                    recv_ty.item_path().map(|p| p == recv_path).unwrap_or(false)
                }
                ImplKind::Trait { base_ty, .. } => {
                    base_ty.item_path().map(|p| p == recv_path).unwrap_or(false)
                }
            })
            .cloned()
            .collect()
    }

    fn external_scheme(&self, def_id: DefId) -> Option<TyScheme> {
        self.external_schemes.get(&def_id).cloned()
    }

    fn resolve_builtin(&self, name: &str) -> ItemPath {
        ItemPath::from(format!("core::{}", name).as_str())
    }

    fn infix_op(&self, _symbol: &str) -> Option<(ItemPath, ItemPath)> {
        None
    }

    fn prefix_op(&self, _symbol: &str) -> Option<(ItemPath, ItemPath)> {
        None
    }

    fn external_local_type(&self, _local_id: LocalBindingId) -> Option<Ty> {
        // Mock doesn't track external local types
        None
    }

    fn def_item_path(&self, _target: &DefTarget) -> Option<ItemPath> {
        // Mock doesn't have access to definition paths
        None
    }

    fn local_bindings_for_group(&self) -> HashMap<NodeId, LocalBindingId> {
        // Mock doesn't track local bindings
        HashMap::new()
    }
}
