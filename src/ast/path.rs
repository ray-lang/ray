use std::{fmt, hash::Hasher, str::Chars};

use itertools::Itertools;

use crate::{
    pathlib::FilePath,
    typing::{ty::TyVar, ApplySubst, Subst},
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum PathPart {
    Name(String),
    TyArgs(String),
}

impl std::fmt::Debug for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) | PathPart::TyArgs(s) => write!(f, "{}", s),
        }
    }
}

impl std::fmt::Display for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) | PathPart::TyArgs(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Clone, Eq, Default, PartialOrd, Ord, Hash)]
pub struct Path {
    parts: Vec<PathPart>,
}

impl PartialEq for Path {
    fn eq(&self, other: &Self) -> bool {
        self.parts == other.parts
    }
}

impl PartialEq<&str> for Path {
    fn eq(&self, other: &&str) -> bool {
        let s = self.to_string();
        &s.as_str() == other
    }
}

impl ApplySubst for Path {
    fn apply_subst(self, subst: &Subst) -> Self {
        let mut parts = vec![];
        for part in self.parts.into_iter() {
            if let PathPart::TyArgs(args) = part {
                let s = args.trim_matches(|ch| ch == '<' || ch == '>');
                let mut args = String::new();
                let mut ret = String::new();
                let mut paren_stack = 0;
                let mut is_args = true;
                for ch in s.chars() {
                    if is_args {
                        match ch {
                            '(' => {
                                paren_stack += 1;
                                continue;
                            }
                            ')' => {
                                paren_stack -= 1;
                                continue;
                            }
                            ':' if paren_stack == 0 => {
                                is_args = false;
                                continue;
                            }
                            _ => (),
                        }
                    }

                    if is_args {
                        args.push(ch);
                    } else {
                        ret.push(ch);
                    }
                }

                let args = args
                    .split(',')
                    .map(|a| {
                        let tv = TyVar(Path::from(a));
                        if let Some(ty) = subst.get(&tv) {
                            ty.clone().to_string()
                        } else {
                            a.to_string()
                        }
                    })
                    .collect::<Vec<_>>();
                let ret = {
                    let tv = TyVar(Path::from(ret.as_str()));
                    if let Some(ty) = subst.get(&tv) {
                        ty.clone().to_string()
                    } else {
                        ret
                    }
                };
                parts.push(PathPart::TyArgs(format!("<({}):{}>", args.join(","), ret)));
            } else {
                parts.push(part);
                let tv = TyVar(Path {
                    parts: parts.clone(),
                });
                if let Some(ty) = subst.get(&tv) {
                    parts = ty
                        .to_string()
                        .split("::")
                        .map(|s| PathPart::Name(s.to_string()))
                        .collect::<Vec<_>>();
                }
            }
        }

        Path { parts }
    }
}

impl Path {
    pub fn new() -> Path {
        Path { parts: vec![] }
    }

    pub fn name(&self) -> Option<String> {
        self.parts.last().map(PathPart::to_string)
    }

    pub fn len(&self) -> usize {
        self.parts.len()
    }

    pub fn to_id(&self) -> u64 {
        let mut h = fnv::FnvHasher::default();
        h.write(self.to_string().as_bytes());
        h.finish()
    }

    pub fn to_vec(&self) -> Vec<String> {
        self.parts.iter().map(|p| p.to_string()).collect()
    }

    pub fn to_filepath(&self) -> FilePath {
        let mut fp = FilePath::new();
        for p in self.parts.iter() {
            fp.push(p.to_string())
        }
        fp.into()
    }

    pub fn with_all(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.push(PathPart::Name(String::from("*")));
        Path { parts }
    }

    pub fn append<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push(PathPart::Name(s.to_string()));
        Path { parts }
    }

    pub fn append_tyargs<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push(PathPart::TyArgs(s.to_string()));
        Path { parts }
    }

    pub fn with_name<T: ToString>(&self, name: T) -> Path {
        let mut parts = self.parts.clone();
        let name = PathPart::Name(name.to_string());
        if let Some(last) = parts.last_mut() {
            *last = name;
        } else {
            parts = vec![name];
        }
        Path { parts }
    }

    pub fn without_tyargs(&self) -> Path {
        let parts = self
            .parts
            .iter()
            .cloned()
            .filter(|p| !matches!(p, PathPart::TyArgs(_)))
            .collect::<Vec<_>>();

        Path { parts }
    }

    pub fn parent(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.pop();
        Path { parts }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.parts.iter().map(PathPart::to_string).join("::")
        )
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            self.parts.iter().map(PathPart::to_string).join("::")
        )
    }
}

impl From<FilePath> for Path {
    fn from(f: FilePath) -> Path {
        Path {
            parts: vec![PathPart::Name(f.file_stem())],
        }
    }
}

impl From<String> for Path {
    fn from(s: String) -> Path {
        let parser = PathParser::new();
        parser.parse(s)
    }
}

impl From<&str> for Path {
    fn from(s: &str) -> Path {
        Path::from(s.to_string())
    }
}

impl From<Vec<String>> for Path {
    fn from(parts: Vec<String>) -> Path {
        Path {
            parts: parts.into_iter().map(PathPart::Name).collect(),
        }
    }
}

impl<T> From<&T> for Path
where
    T: Clone,
    Path: From<T>,
{
    fn from(v: &T) -> Self {
        Path::from(v.clone())
    }
}

struct PathParser {
    parts: Vec<PathPart>,
    curr_part: String,
}

impl PathParser {
    fn new() -> PathParser {
        PathParser {
            parts: vec![],
            curr_part: String::new(),
        }
    }

    fn parse(mut self, s: String) -> Path {
        let mut chars = s.chars();
        loop {
            match chars.next() {
                Some(':') => {
                    self.maybe_finish_part(&mut chars);
                }
                Some('<') => self.parse_ty_args(&mut chars),
                Some(ch) => self.curr_part.push(ch),
                _ => {
                    self.push_part();
                    break;
                }
            }
        }

        Path { parts: self.parts }
    }

    fn parse_ty_args(&mut self, chars: &mut Chars) {
        self.curr_part.push('<');
        loop {
            match chars.next() {
                Some(ch) if ch == '<' || ch == '>' || ch == ':' => {
                    self.curr_part.push(ch);
                    break;
                }
                Some(ch) => self.curr_part.push(ch),
                _ => break,
            }
        }
    }

    fn maybe_finish_part(&mut self, chars: &mut Chars) -> bool {
        match chars.next() {
            Some(':') | None => {
                self.push_part();
                true
            }
            Some(ch) => {
                self.curr_part.push(':');
                self.curr_part.push(ch);
                false
            }
        }
    }

    fn push_part(&mut self) {
        let part = std::mem::take(&mut self.curr_part);
        let part = if part.starts_with('<') && part.ends_with('>') {
            PathPart::TyArgs(part)
        } else {
            PathPart::Name(part)
        };
        self.parts.push(part);
    }
}

#[macro_export]
macro_rules! path {
    ($($x:expr),*) => (Path::from(vec![$(String::from($x),)*]))
}
