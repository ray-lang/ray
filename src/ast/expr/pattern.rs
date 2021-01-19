use crate::{
    ast::{Name, Sequence},
    span::Span,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PatternKind<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Name(Name),
    Sequence(Sequence<Info>),
    Tuple(Sequence<Info>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub kind: PatternKind<Info>,
    pub span: Span,
}

impl<Info> std::fmt::Display for Pattern<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match &self.kind {
                PatternKind::Name(n) => n.to_string(),
                PatternKind::Sequence(seq) => seq.to_string(),
                PatternKind::Tuple(seq) => format!("(tuple ({}))", seq),
            }
        )
    }
}
