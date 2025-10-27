use std::fmt;

use serde::{Deserialize, Serialize};

pub mod parsed;
mod source;

pub use source::*;

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct Pos {
    pub lineno: usize,
    pub col: usize,
    pub offset: usize,
}

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct Span {
    pub start: Pos,
    pub end: Pos,
}

impl Span {
    pub fn new() -> Span {
        Span {
            start: Pos::empty(),
            end: Pos::empty(),
        }
    }

    pub fn at(pos: Pos) -> Span {
        Span {
            start: pos,
            end: pos,
        }
    }

    pub fn lines(&self) -> usize {
        (self.end.lineno - self.start.lineno) + 1
    }

    pub fn len(&self) -> usize {
        self.end.offset - self.start.offset
    }

    pub fn sub(&self, offset: usize) -> Span {
        let mut end = self.end;
        end.offset -= offset;
        Span {
            start: self.start,
            end,
        }
    }

    /// Create a new span with the start of this one and end of another one
    pub fn extend_to(&self, other: &Span) -> Span {
        Span {
            start: self.start,
            end: other.end,
        }
    }

    pub fn contains_pos(&self, pos: &Pos) -> bool {
        (pos.offset >= self.start.offset) && (pos.offset <= self.end.offset)
    }

    pub fn contains_line_col(&self, line: usize, col: usize) -> bool {
        if line < self.start.lineno || line > self.end.lineno {
            return false;
        }
        if line == self.start.lineno && col < self.start.col {
            return false;
        }
        if line == self.end.lineno && col > self.end.col {
            return false;
        }
        true
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
    pub fn empty() -> Pos {
        Pos {
            lineno: 0,
            col: 0,
            offset: 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.lineno == 0 && self.col == 0 && self.offset == 0
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.lineno + 1, self.col + 1)
    }
}

#[cfg(test)]
mod tests {
    use super::{Pos, Span};

    fn span(start: Pos, end: Pos) -> Span {
        Span { start, end }
    }

    fn pos(lineno: usize, col: usize) -> Pos {
        Pos {
            lineno,
            col,
            offset: 0,
        }
    }

    #[test]
    fn span_contains_line_col() {
        let s1 = span(pos(2, 5), pos(4, 10));

        assert!(!s1.contains_line_col(1, 0));
        assert!(!s1.contains_line_col(5, 0));

        assert!(!s1.contains_line_col(2, 4));
        assert!(s1.contains_line_col(2, 5));
        assert!(s1.contains_line_col(2, 10));
        assert!(s1.contains_line_col(2, 15));

        assert!(s1.contains_line_col(3, 0));

        assert!(s1.contains_line_col(4, 0));
        assert!(s1.contains_line_col(4, 5));
        assert!(s1.contains_line_col(4, 10));
        assert!(!s1.contains_line_col(4, 11));

        let s2 = span(pos(2, 0), pos(2, 10));
        assert!(!s2.contains_line_col(2, 11));
        assert!(s2.contains_line_col(2, 10));
        assert!(s2.contains_line_col(2, 0));
        assert!(!s2.contains_line_col(2, usize::MAX));
        assert!(!s2.contains_line_col(1, 0));
        assert!(!s2.contains_line_col(3, 0));

        let s3 = span(pos(0, 0), pos(0, 0));
        assert!(s3.contains_line_col(0, 0));
        assert!(!s3.contains_line_col(0, 1));
        assert!(!s3.contains_line_col(1, 0));
    }
}
