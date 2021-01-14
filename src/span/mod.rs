use std::fmt;

use crate::pathlib::FilePath;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub lineno: usize,
    pub col: usize,
    pub offset: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    pub start: Pos,
    pub end: Pos,
}

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Source {
    pub filepath: FilePath,
    pub span: Option<Span>,
}

impl Source {
    pub fn extend_to(&self, other: &Source) -> Source {
        let span = match (self.span, other.span) {
            (Some(a), Some(b)) => Some(a.extend_to(&b)),
            (Some(a), _) => Some(a),
            (_, Some(b)) => Some(b),
            _ => None,
        };

        Source {
            span,
            filepath: self.filepath.clone(),
        }
    }
}

impl Span {
    pub fn new() -> Span {
        Span {
            start: Pos::new(),
            end: Pos::new(),
        }
    }

    pub fn lines(&self) -> usize {
        (self.end.lineno - self.start.lineno) + 1
    }

    pub fn len(&self) -> usize {
        self.end.offset - self.start.offset
    }

    /// Create a new span with the start of this one and end of another one
    pub fn extend_to(&self, other: &Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.start)
    }
}

impl From<Pos> for Span {
    fn from(p: Pos) -> Span {
        Span { start: p, end: p }
    }
}

impl Pos {
    pub fn new() -> Pos {
        Pos {
            lineno: 0,
            col: 0,
            offset: 0,
        }
    }

    pub fn empty(&self) -> bool {
        self.lineno == 0 && self.col == 0 && self.offset == 0
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.lineno + 1, self.col + 1)
    }
}
