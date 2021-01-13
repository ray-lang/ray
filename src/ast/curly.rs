use crate::{span::Span, strutils::indent_lines, utils::join};

use super::{Expr, Name};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CurlyElementKind {
    Name(Name),
    Labeled(Name, Expr),
}

impl std::fmt::Display for CurlyElementKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CurlyElementKind::Name(n) => write!(f, "{}", n),
            CurlyElementKind::Labeled(n, ex) => write!(f, "{}: {}", n, ex),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurlyElement {
    pub kind: CurlyElementKind,
    pub span: Span,
}

impl std::fmt::Display for CurlyElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Curly {
    pub lhs: Option<Name>,
    pub elements: Vec<CurlyElement>,
    pub curly_span: Span,
}

impl std::fmt::Display for Curly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (sep, multiline) = if self.elements.len() > 3 {
            (",\n", true)
        } else {
            (", ", false)
        };

        let elements = join(self.elements.iter(), sep);
        let body = if multiline {
            format!("{{\n{}\n}}", indent_lines(elements, 2))
        } else if elements.len() != 0 {
            format!("{{ {} }}", elements)
        } else {
            format!("{{}}")
        };

        if let Some(lhs) = &self.lhs {
            write!(f, "({} {})", lhs, body)
        } else {
            write!(f, "{}", body)
        }
    }
}
