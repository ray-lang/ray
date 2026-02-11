use serde::{Deserialize, Serialize};

use crate::{local_binding::LocalBindingId, pathlib::ModulePath, resolution::DefTarget};

/// An entry in the scope visible at a given position.
///
/// Used by the `scope_at` query to report what names are available
/// for completion and other IDE features.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ScopeEntry {
    /// A local binding (parameter or let-binding).
    Local(LocalBindingId),
    /// A top-level definition (function, struct, trait, etc.) or an import.
    Def(DefTarget),
    /// A namespace import (e.g., `import utils` makes `utils` a module handle).
    Module(ModulePath),
}
