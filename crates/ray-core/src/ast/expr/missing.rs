use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Missing {
    pub expected: String,
    pub context: Option<String>,
}

impl Missing {
    pub fn new(expected: impl Into<String>, context: Option<impl Into<String>>) -> Self {
        Self {
            expected: expected.into(),
            context: context.map(Into::into),
        }
    }
}

impl std::fmt::Display for Missing {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.context {
            Some(ctx) => write!(f, "(missing {} in {})", self.expected, ctx),
            None => write!(f, "(missing {})", self.expected),
        }
    }
}
