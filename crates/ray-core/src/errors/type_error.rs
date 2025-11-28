use ray_typing::TypeError;

use super::{RayError, RayErrorKind};

impl From<TypeError> for RayError {
    fn from(err: TypeError) -> Self {
        let msg = err.message_str();
        let src = err.info.source;
        RayError {
            msg,
            src,
            kind: RayErrorKind::Type,
            context: Some("type checking".to_string()),
        }
    }
}
