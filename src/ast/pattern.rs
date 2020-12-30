use crate::ast::{Name, Sequence};
use crate::span::Span;

#[derive(Clone, Debug)]
pub enum PatternKind {
    Name(Name),
    Sequence(Sequence),
    Tuple(Sequence),
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

impl std::fmt::Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self.kind {
                PatternKind::Name(ref n) => n.to_string(),
                PatternKind::Sequence(ref seq) => seq.to_string(),
                PatternKind::Tuple(ref seq) => format!("(tuple ({}))", seq),
            }
        )
    }
}
