use crate::span::Span;

#[derive(Debug)]
pub struct Symbol {
    pub name: String,
    pub span: Span,
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(symbol {})", self.name)
    }
}
