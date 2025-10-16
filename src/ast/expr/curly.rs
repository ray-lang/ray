use crate::{
    ast::{Expr, Name, Node, Path},
    span::{Span, parsed::Parsed},
    strutils::indent_lines,
    typing::ty::TyScheme,
    utils::join,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CurlyElement {
    Name(Name),
    Labeled(Name, Node<Expr>),
}

impl std::fmt::Display for CurlyElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CurlyElement::Name(n) => write!(f, "{}", n),
            CurlyElement::Labeled(n, ex) => write!(f, "{}: {}", n, ex),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Curly {
    pub lhs: Option<Parsed<Path>>,
    pub elements: Vec<Node<CurlyElement>>,
    pub curly_span: Span,
    pub ty: TyScheme,
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
