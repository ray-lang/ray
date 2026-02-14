use ray_shared::resolution::DefTarget;
use serde::{Deserialize, Serialize};

use crate::types::{Subst, TyScheme};

/// Resolved call target information.
///
/// For trait methods, `trait_target` is set to the trait method's DefTarget,
/// and `impl_target` is set to the specific impl method if it's known at
/// type-check time (i.e., for monomorphic receiver types). For polymorphic
/// receivers, `impl_target` is `None` and dispatch happens at instantiation.
///
/// For inherent methods, `trait_target` is `None` and `impl_target` is set
/// to the method's DefTarget.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CallResolution {
    /// The trait method target, if this call is a trait method.
    pub trait_target: Option<DefTarget>,
    /// The impl/inherent method target, if known.
    pub impl_target: Option<DefTarget>,
    pub poly_callee_ty: TyScheme,
    pub callee_ty: TyScheme,
    pub subst: Subst,
}

impl CallResolution {
    /// Returns the most specific target available.
    ///
    /// Prefers `impl_target` (for codegen when the impl is known), falling back
    /// to `trait_target` (for polymorphic dispatch).
    pub fn target(&self) -> Option<&DefTarget> {
        self.impl_target.as_ref().or(self.trait_target.as_ref())
    }
}
