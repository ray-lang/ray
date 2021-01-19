use crate::ast::Sequence;

pub struct Tuple<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub seq: Sequence<Info>,
}

impl<Info> std::fmt::Display for Tuple<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(tuple ({}))", self.seq)
    }
}
