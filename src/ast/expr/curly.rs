use crate::{
    ast::{Expr, Name, Node},
    span::Span,
    strutils::indent_lines,
    utils::join,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CurlyElementKind<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    Name(Name),
    Labeled(Name, Node<Expr<Info>, Info>),
}

impl<Info> std::fmt::Display for CurlyElementKind<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CurlyElementKind::Name(n) => write!(f, "{}", n),
            CurlyElementKind::Labeled(n, ex) => write!(f, "{}: {}", n, ex),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CurlyElement<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub kind: CurlyElementKind<Info>,
    pub span: Span,
}

impl<Info> std::fmt::Display for CurlyElement<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Curly<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
    pub lhs: Option<Name>,
    pub elements: Vec<CurlyElement<Info>>,
    pub curly_span: Span,
}

impl<Info> std::fmt::Display for Curly<Info>
where
    Info: std::fmt::Debug + Clone + PartialEq + Eq,
{
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
