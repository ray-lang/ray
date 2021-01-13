#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Nil;

impl std::fmt::Display for Nil {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "nil")
    }
}
