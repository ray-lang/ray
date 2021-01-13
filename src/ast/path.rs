use std::fmt;
use std::hash::Hasher;

use crate::pathlib::FilePath;
use crate::span::Span;

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Path {
    parts: Vec<String>,
    pub span: Span,
}

impl Path {
    pub fn new() -> Path {
        Path {
            parts: vec![],
            span: Span::new(),
        }
    }

    pub fn name(&self) -> Option<&String> {
        self.parts.last()
    }

    pub fn contains(&self, part: &str) -> bool {
        self.parts.contains(&String::from(part))
    }

    pub fn to_id(&self) -> u64 {
        let mut h = fnv::FnvHasher::default();
        h.write(self.to_string().as_bytes());
        h.finish()
    }

    pub fn to_filepath(&self) -> FilePath {
        let mut fp = FilePath::new();
        for p in self.parts.iter() {
            fp.push(p)
        }
        fp.into()
    }

    pub fn with_all(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.push(String::from("*"));
        Path {
            parts,
            span: self.span,
        }
    }

    pub fn append<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push(s.to_string());
        Path {
            parts,
            span: self.span,
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.parts.join("::"))
    }
}

impl From<&FilePath> for Path {
    fn from(f: &FilePath) -> Path {
        Path {
            parts: vec![f.file_stem()],
            span: Span::new(),
        }
    }
}

impl From<&String> for Path {
    fn from(s: &String) -> Path {
        let parts = s.split("::").map(|s| s.to_string()).collect();
        Path {
            parts,
            span: Span::new(),
        }
    }
}

impl From<&str> for Path {
    fn from(s: &str) -> Path {
        let parts = s.split("::").map(|s| s.to_string()).collect();
        Path {
            parts,
            span: Span::new(),
        }
    }
}

impl From<Vec<String>> for Path {
    fn from(parts: Vec<String>) -> Path {
        Path {
            parts,
            span: Span::new(),
        }
    }
}

#[macro_export]
macro_rules! path {
    ($($x:expr),*) => (Path::from(vec![$(String::from($x),)*]))
}
