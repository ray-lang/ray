// Global environment for traits, structs, impls, and other predicates.

use std::collections::{BTreeMap, HashMap};

use ray_shared::{
    def::DefId,
    local_binding::LocalBindingId,
    node_id::NodeId,
    pathlib::{ItemPath, Path},
    resolution::DefTarget,
    ty::Ty,
};
use serde::{Deserialize, Serialize};

use crate::types::{
    ImplField, ImplTy, StructTy, Subst, Substitutable, TraitField, TraitTy, TyScheme,
};

/// Environment trait for typechecking that abstracts over definition lookups.
///
/// This trait allows the typechecker to be decoupled from the query system.
/// The query layer implements this trait to provide definition lookups via queries,
/// while the typechecker core only depends on these abstract methods.
///
/// The typechecker extracts `ItemPath` from `Ty` using `ty.item_path()` before
/// calling these methods. The implementing layer then converts `ItemPath` to
/// `DefTarget` internally for efficient lookups.
pub trait TypecheckEnv {
    /// Look up a struct definition by its path.
    fn struct_def(&self, path: &ItemPath) -> Option<StructTy>;

    /// Look up a trait definition by its path.
    fn trait_def(&self, path: &ItemPath) -> Option<TraitTy>;

    /// Find all trait definitions in the environment.
    fn all_traits(&self) -> Vec<TraitTy>;

    /// Get all implementations of a trait.
    fn impls_for_trait(&self, trait_path: &ItemPath) -> Vec<ImplTy>;

    /// Get all inherent implementations for a type.
    fn inherent_impls(&self, type_path: &ItemPath) -> Vec<ImplTy>;

    /// Get all implementations for a given receiver type.
    fn impls_for_recv(&self, recv_path: &ItemPath) -> Vec<ImplTy>;

    /// Look up the type scheme for a definition outside the current binding group.
    ///
    /// This is used for cross-group dependencies during typechecking.
    fn external_scheme(&self, def_id: DefId) -> Option<TyScheme>;

    /// Look up the type for a local binding outside the current binding group.
    ///
    /// This is used when a definition references a local binding owned by another
    /// definition (e.g., a function referencing a top-level assignment in FileMain).
    /// The query system ensures the owner's binding group is typechecked first.
    fn external_local_type(&self, local_id: LocalBindingId) -> Option<Ty>;

    /// Resolve a builtin type name to its definition path.
    ///
    /// This performs name resolution in the current context for builtin types
    /// like `list`, `dict`, `set`, `range`, and builtin traits like `Index`,
    /// `Deref`, `Hash`, `Eq`, `Iterable`, `Iter`.
    ///
    /// Primitives (int, float, bool) are handled separately as they're built
    /// into `Ty` directly.
    ///
    /// If the name cannot be resolved, defaults to `core::{name}`.
    fn resolve_builtin(&self, name: &str) -> ItemPath;

    /// Look up the trait and method paths for an infix operator symbol.
    ///
    /// Returns `(trait_path, method_path)` for operators like `+`, `-`, `*`, etc.
    fn infix_op(&self, symbol: &str) -> Option<(ItemPath, ItemPath)>;

    /// Look up the trait and method paths for a prefix operator symbol.
    ///
    /// Returns `(trait_path, method_path)` for operators like `-` (negation), `!`, etc.
    fn prefix_op(&self, symbol: &str) -> Option<(ItemPath, ItemPath)>;

    /// Get the fully qualified ItemPath for a definition target.
    ///
    /// This is used during lowering to convert resolved names (stored as DefTarget)
    /// into their canonical paths for use in the type system.
    fn def_item_path(&self, target: &DefTarget) -> Option<ItemPath>;

    /// Get all NodeId → LocalBindingId mappings for the current binding group.
    ///
    /// This is used by the copy step after type inference to populate `node_tys`
    /// from `local_tys`. Returns all nodes in the current group that resolve to
    /// local bindings (parameters, let-bindings, closure captures, etc.).
    fn local_bindings_for_group(&self) -> HashMap<NodeId, LocalBindingId>;

    /// Resolve the type embedded in an expression (e.g., the target type of a cast).
    ///
    /// This applies name resolutions and type parameter mappings to produce a
    /// fully resolved type from expression-level type references like `x as rawptr['k]`.
    fn resolved_expr_ty(&self, node_id: NodeId) -> Option<Ty>;
}

#[derive(
    Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize,
)]
pub struct ImplIndex(usize);

impl ImplIndex {
    pub fn as_usize(self) -> usize {
        self.0
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GlobalEnv {
    pub structs: HashMap<String, StructTy>,
    pub traits: HashMap<String, TraitTy>,
    pub impls: Vec<ImplTy>,
    pub impls_by_trait: BTreeMap<ItemPath, Vec<ImplIndex>>,
    pub impls_by_recv: BTreeMap<String, Vec<ImplIndex>>,
    pub inherent_impls: BTreeMap<String, Vec<ImplIndex>>,
    /// Mapping from binary operator symbols (e.g. "+") to the name of the
    /// trait that governs them (e.g. "Add"). This is populated in the same
    /// place as the old TyCtx operator tables during trait lowering.
    pub infix_ops: HashMap<String, (Path, Path)>,
    /// Mapping from unary operator symbols (e.g. "-") to the name of the
    /// trait that governs them (e.g. "Neg").
    pub prefix_ops: HashMap<String, (Path, Path)>,
}

impl GlobalEnv {
    pub fn new() -> Self {
        GlobalEnv::default()
    }

    pub fn get_struct(&self, name: &str) -> Option<&StructTy> {
        self.structs.get(name)
    }

    pub fn get_trait(&self, name: &str) -> Option<&TraitTy> {
        self.traits.get(name)
    }

    pub fn resolve_impl_from_index(&self, idx: &ImplIndex) -> Option<&ImplTy> {
        self.impls.get(idx.as_usize())
    }

    pub fn resolve_impl_from_index_mut(&mut self, idx: &ImplIndex) -> Option<&mut ImplTy> {
        self.impls.get_mut(idx.as_usize())
    }

    pub fn impls_for_trait(&self, _trait_name: &str) -> Vec<&ImplTy> {
        unreachable!("DO NOT REMOVE THIS PANIC: legacy code should not be called")

        // self.impls_by_trait
        //     .get(trait_name)
        //     .into_iter()
        //     .flatten()
        //     .flat_map(|idx| self.resolve_impl_from_index(idx))
    }

    pub fn inherent_impls_for_key(&self, key: &str) -> impl Iterator<Item = &ImplTy> {
        self.inherent_impls
            .get(key)
            .into_iter()
            .flatten()
            .flat_map(|idx| self.resolve_impl_from_index(idx))
    }

    pub fn add_impl(&mut self, _impl_ty: ImplTy) {
        unreachable!("DO NOT REMOVE THIS PANIC: legacy code should not be called")

        // match &impl_ty.kind {
        //     ImplKind::Inherent { recv_ty } => {
        //         let fqn = match recv_ty {
        //             Ty::Const(p) | Ty::Proj(p, _) => p.to_string(),
        //             _ => return,
        //         };

        //         let idx = ImplIndex(self.impls.len());
        //         self.impls.push(impl_ty);
        //         self.inherent_impls.entry(fqn).or_default().push(idx)
        //     }
        //     ImplKind::Trait {
        //         trait_ty, base_ty, ..
        //     } => {
        //         let trait_name = match trait_ty {
        //             Ty::Const(p) | Ty::Proj(p, _) => p.to_string(),
        //             _ => return,
        //         };

        //         log::debug!(
        //             "[add_impl] trait_name = {}, impl_ty = {:?}",
        //             trait_name,
        //             impl_ty
        //         );

        //         let recv_name = base_ty.get_path().to_string();
        //         let idx = ImplIndex(self.impls.len());
        //         self.impls.push(impl_ty);
        //         self.impls_by_trait.entry(trait_name).or_default().push(idx);
        //         self.impls_by_recv.entry(recv_name).or_default().push(idx);
        //     }
        // }
    }

    /// Register a binary operator symbol and its trait name.
    pub fn register_infix_op(
        &mut self,
        symbol: impl Into<String>,
        method_fqn: Path,
        trait_fqn: Path,
    ) {
        self.infix_ops
            .insert(symbol.into(), (method_fqn, trait_fqn));
    }

    /// Register a unary operator symbol and its trait name.
    pub fn register_prefix_op(
        &mut self,
        symbol: impl Into<String>,
        method_fqn: Path,
        trait_fqn: Path,
    ) {
        self.prefix_ops
            .insert(symbol.into(), (method_fqn, trait_fqn));
    }

    /// Look up the trait name for a binary operator symbol, if any.
    pub fn infix_trait_for(&self, symbol: &str) -> Option<&Path> {
        self.infix_ops.get(symbol).map(|(_, trait_fqn)| trait_fqn)
    }

    /// Look up the method and trait FQNs for a binary operator symbol, if any.
    pub fn lookup_infix_op(&self, symbol: &str) -> Option<(&Path, &Path)> {
        self.infix_ops
            .get(symbol)
            .map(|(method_fqn, trait_fqn)| (method_fqn, trait_fqn))
    }

    /// Look up the method and trait FQNs for a unary operator symbol, if any.
    pub fn lookup_prefix_op(&self, symbol: &str) -> Option<(&Path, &Path)> {
        self.prefix_ops
            .get(symbol)
            .map(|(method_fqn, trait_fqn)| (method_fqn, trait_fqn))
    }

    /// Look up the trait name for a unary operator symbol, if any.
    pub fn prefix_trait_for(&self, symbol: &str) -> Option<&Path> {
        self.prefix_ops.get(symbol).map(|(_, trait_fqn)| trait_fqn)
    }

    /// Look up the trait method, if any.
    pub fn resolve_trait_methods(&self, method_name: &str) -> Vec<(&TraitTy, &TraitField)> {
        self.traits
            .values()
            .filter_map(|trait_ty| trait_ty.get_field(method_name).map(|f| (trait_ty, f)))
            .collect()
    }

    /// Look up the inherent trait method, if any.
    pub fn resolve_inherent_methods(&self, method_name: &str) -> Vec<(&ImplTy, &ImplField)> {
        self.inherent_impls
            .values()
            .flatten()
            .filter_map(|idx| {
                let Some(impl_ty) = self.resolve_impl_from_index(idx) else {
                    return None;
                };
                impl_ty.fields.iter().find_map(|field| {
                    let Some(name) = field.path.item_name() else {
                        return None;
                    };

                    if name == method_name {
                        Some((impl_ty, field))
                    } else {
                        None
                    }
                })
            })
            .collect()
    }

    /// Apply a type substitution to all nominal metadata stored in this
    /// instance environment. This is primarily useful for debugging or
    /// for scenarios where we want to view the environment through the
    /// lens of a particular substitution (it should not typically be
    /// mutated during normal solving).
    pub fn apply_subst(&mut self, subst: &Subst) {
        for s in self.structs.values_mut() {
            s.apply_subst(subst);
        }

        for t in self.traits.values_mut() {
            t.apply_subst(subst);
        }

        for impl_ty in self.impls.iter_mut() {
            impl_ty.apply_subst(subst);
        }
    }

    /// Extend this environment with definitions from another environment.
    /// Existing entries are preserved; new ones are merged in.
    pub fn extend(&mut self, other: GlobalEnv) {
        for (name, struct_ty) in other.structs {
            self.structs.entry(name).or_insert(struct_ty);
        }

        for (name, trait_ty) in other.traits {
            self.traits.entry(name).or_insert(trait_ty);
        }

        let mut impl_reindex = HashMap::new();
        for (idx, impl_ty) in other.impls.into_iter().enumerate() {
            let new_idx = ImplIndex(self.impls.len());
            self.impls.push(impl_ty);
            impl_reindex.insert(ImplIndex(idx), new_idx);
        }

        for (trait_name, impls) in other.impls_by_trait {
            self.impls_by_trait
                .entry(trait_name)
                .or_default()
                .extend(impls.into_iter().map(|idx| impl_reindex[&idx]));
        }

        for (recv_fqn, impls) in other.impls_by_recv {
            self.impls_by_recv
                .entry(recv_fqn)
                .or_default()
                .extend(impls.into_iter().map(|idx| impl_reindex[&idx]));
        }

        for (fqn, impls) in other.inherent_impls {
            self.inherent_impls
                .entry(fqn)
                .or_default()
                .extend(impls.into_iter().map(|idx| impl_reindex[&idx]));
        }

        self.infix_ops.extend(other.infix_ops.into_iter());
        self.prefix_ops.extend(other.prefix_ops.into_iter());
    }
}
