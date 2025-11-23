use ray_typing::error::TypeError;

use super::{RayError, RayErrorKind};

impl From<TypeError> for RayError {
    fn from(err: TypeError) -> Self {
        RayError {
            msg: err.message(),
            src: err.src,
            kind: RayErrorKind::Type,
            context: Some("type checking".to_string()),
        }
    }
}
