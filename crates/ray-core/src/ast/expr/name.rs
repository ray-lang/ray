use std::hash::Hash;

use ray_shared::pathlib::Path;
use serde::{Deserialize, Serialize};

use ray_shared::span::parsed::Parsed;
use ray_typing::types::TyScheme;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Name {
    pub path: Path,
    pub ty: Option<Parsed<TyScheme>>,
}

impl PartialOrd for Name {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.path.partial_cmp(&other.path)
    }
}

impl Ord for Name {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.path.cmp(&other.path)
    }
}

impl Hash for Name {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.path.hash(state);
    }
}

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref t) = self.ty {
            write!(f, "{}: {}", self.path, t)
        } else {
            write!(f, "{}", self.path)
        }
    }
}

impl Name {
    pub fn new<P: Into<Path>>(path: P) -> Name {
        Name {
            path: path.into(),
            ty: None,
        }
    }

    pub fn typed<P: Into<Path>>(path: P, ty: Parsed<TyScheme>) -> Name {
        Name {
            path: path.into(),
            ty: Some(ty),
        }
    }
}
