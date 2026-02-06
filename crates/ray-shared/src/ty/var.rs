use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

use serde::{Deserialize, Serialize};

use crate::pathlib::Path;

pub const SCHEMA_PREFIX: &'static str = "?s";
pub const SKOLEM_PREFIX: &'static str = "?k";

/// Shared allocator for schema variables (`?sN`).
///
/// Both the frontend lowering context and the solver need to mint fresh
/// schema variables, so we keep the allocator tiny and share it via `Rc`.
///
/// For incremental compilation, use `with_def_scope` to create an allocator
/// that produces deterministic variable names scoped to a specific definition.
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct SchemaVarAllocator {
    next_id: u32,
    /// Optional prefix for scoped allocation (e.g., "?s:abc123:" for DefId-scoped vars)
    #[serde(default)]
    prefix: Option<String>,
}

impl SchemaVarAllocator {
    pub fn new() -> Self {
        SchemaVarAllocator {
            next_id: 0,
            prefix: None,
        }
    }

    /// Create an allocator scoped to a specific DefId.
    ///
    /// Produces deterministic variable names like `?s:{hex_hash}:{index}` where
    /// the hex hash is derived from the DefId. This ensures uniqueness across
    /// definitions without requiring global mutable state.
    pub fn with_def_scope(def_id: crate::def::DefId) -> Self {
        let mut hasher = DefaultHasher::new();
        def_id.hash(&mut hasher);
        let hash = hasher.finish();
        let prefix = format!("{}:{:x}:", SCHEMA_PREFIX, hash);
        SchemaVarAllocator {
            next_id: 0,
            prefix: Some(prefix),
        }
    }

    pub fn alloc(&mut self) -> TyVar {
        let name = if let Some(ref prefix) = self.prefix {
            format!("{}{}", prefix, self.next_id)
        } else {
            format!("{}{}", SCHEMA_PREFIX, self.next_id)
        };
        self.next_id += 1;
        TyVar::new(name)
    }

    pub fn curr_id(&self) -> u32 {
        self.next_id
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TyVar(pub Path);

impl TyVar {
    pub fn new<P: Into<Path>>(p: P) -> TyVar {
        TyVar(p.into())
    }

    #[inline(always)]
    pub fn path(&self) -> &Path {
        &self.0
    }

    #[inline(always)]
    pub fn path_mut(&mut self) -> &mut Path {
        &mut self.0
    }

    /// Returns true if this variable name looks like a "meta" variable
    /// (e.g. "?t0"), following the current naming convention. We also
    /// treat return-placeholders (e.g. "%r0") as metas so they can
    /// participate in unification and be solved like other unknowns.
    ///
    /// Schema variables (e.g. "?s0") and skolems (e.g. "?k0") are rigid and
    /// must not be treated as metas.
    pub fn is_meta(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            // NOTE: skolems (e.g. "?k0") are unknowns but are not solvable
            // metas; they must be treated as rigid.
            return name.starts_with("?t") || name.starts_with("%r");
        }
        false
    }

    /// Returns true if this variable is used as a placeholder for a return
    /// type in the current naming scheme (e.g. "%r0").
    pub fn is_ret_placeholder(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("%r");
        }
        false
    }

    /// Returns true if this variable name is some form of unknown (any name
    /// starting with "?").
    pub fn is_unknown(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with("?");
        }
        false
    }

    /// Returns true if this variable name represents a skolem introduced
    /// during annotation checking (currently `{SKOLEM_PREFIX}*`).
    pub fn is_skolem(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with(SKOLEM_PREFIX);
        }
        false
    }

    /// Returns true if this variable name represents a schema variable
    pub fn is_schema(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with(SCHEMA_PREFIX);
        }
        false
    }

    /// Returns true if this variable is rigid (i.e. not assignable by
    /// unification). Both schema variables (`?sN`) and skolems (`?kN`) are
    /// rigid.
    pub fn is_rigid(&self) -> bool {
        self.is_schema() || self.is_skolem()
    }

    /// Returns true if this is a user-written type variable (e.g. `'a`, `'b`).
    pub fn is_user_var(&self) -> bool {
        if let Some(name) = self.path().name().as_ref() {
            return name.starts_with('\'');
        }
        false
    }
}

impl std::fmt::Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<&str> for TyVar {
    fn from(value: &str) -> Self {
        TyVar(value.into())
    }
}

impl Default for TyVar {
    fn default() -> Self {
        Self(Default::default())
    }
}
