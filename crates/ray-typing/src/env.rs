// Global environment for traits, structs, impls, and other predicates.

use std::collections::{BTreeMap, HashMap};

use ray_shared::{pathlib::Path, ty::Ty};
use serde::{Deserialize, Serialize};

use crate::types::{
    ImplField, ImplKind, ImplTy, StructTy, Subst, Substitutable, TraitField, TraitTy,
};

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GlobalEnv {
    pub structs: HashMap<String, StructTy>,
    pub traits: HashMap<String, TraitTy>,
    pub impls_by_trait: BTreeMap<String, Vec<ImplTy>>,
    pub inherent_impls: BTreeMap<String, Vec<ImplTy>>,
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

    pub fn impls_for_trait(&self, trait_name: &str) -> impl Iterator<Item = &ImplTy> {
        self.impls_by_trait.get(trait_name).into_iter().flatten()
    }

    pub fn add_impl(&mut self, impl_ty: ImplTy) {
        match &impl_ty.kind {
            ImplKind::Inherent { recv_ty } => {
                let fqn = match recv_ty {
                    Ty::Const(p) | Ty::Proj(p, _) => p.to_string(),
                    _ => return,
                };

                self.inherent_impls.entry(fqn).or_default().push(impl_ty)
            }
            ImplKind::Trait { trait_ty, .. } => {
                let trait_name = match trait_ty {
                    Ty::Const(p) | Ty::Proj(p, _) => p.to_string(),
                    _ => return,
                };

                log::debug!(
                    "[add_impl] trait_name = {}, impl_ty = {:?}",
                    trait_name,
                    impl_ty
                );
                self.impls_by_trait
                    .entry(trait_name)
                    .or_default()
                    .push(impl_ty);
            }
        }
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
            .filter_map(|impl_ty| {
                impl_ty.fields.iter().find_map(|field| {
                    let Some(name) = field.path.name() else {
                        return None;
                    };

                    if &name == method_name {
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
        for bucket in self.impls_by_trait.values_mut() {
            for impl_ty in bucket {
                impl_ty.apply_subst(subst);
            }
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
        for (trait_name, bucket) in other.impls_by_trait {
            self.impls_by_trait
                .entry(trait_name)
                .or_default()
                .extend(bucket);
        }
        for (fqn, impls) in other.inherent_impls {
            self.inherent_impls.entry(fqn).or_default().extend(impls);
        }
        self.infix_ops.extend(other.infix_ops.into_iter());
        self.prefix_ops.extend(other.prefix_ops.into_iter());
    }
}
