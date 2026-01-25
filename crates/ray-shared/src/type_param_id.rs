use serde::{Deserialize, Serialize};

use crate::def::DefId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeParamId {
    /// The definition that declares this type parameter
    pub owner: DefId,
    /// Index of this type parameter in the definition's type parameter list
    pub index: u32,
}
