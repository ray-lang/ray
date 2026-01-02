use serde::{Deserialize, Serialize};

use crate::pathlib::Path;

pub const SCHEMA_PREFIX: &'static str = "?s";
pub const SKOLEM_PREFIX: &'static str = "?k";

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
