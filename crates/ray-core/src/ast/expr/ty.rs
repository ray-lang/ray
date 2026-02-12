use std::fmt;

use ray_shared::{
    span::{Span, parsed::Parsed},
    ty::Ty,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TypeParams {
    pub tys: Vec<Parsed<Ty>>,
    pub lb_span: Span,
    pub rb_span: Span,
}

impl fmt::Display for TypeParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}]",
            self.tys
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}
