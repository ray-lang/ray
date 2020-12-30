use crate::ast::Sequence;

#[derive(Clone, Debug)]
pub struct Tuple {
    pub seq: Sequence,
}

impl std::fmt::Display for Tuple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(tuple ({}))", self.seq)
    }
}
