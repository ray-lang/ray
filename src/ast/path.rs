use std::{fmt, hash::Hasher, str::Chars};

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use top::{Subst, Substitutable};

use crate::{
    pathlib::FilePath,
    typing::ty::{Ty, TyVar},
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
enum PathPart {
    Name(String),
    TypeArgs(String),
    FuncType(String),
}

impl std::fmt::Debug for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) | PathPart::TypeArgs(s) | PathPart::FuncType(s) => write!(f, "{}", s),
        }
    }
}

impl std::fmt::Display for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) | PathPart::TypeArgs(s) | PathPart::FuncType(s) => write!(f, "{}", s),
        }
    }
}

#[derive(Clone, Eq, Default, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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

impl Substitutable<TyVar, Ty> for Path {
    fn apply_subst(&mut self, subst: &Subst<TyVar, Ty>) {
        let mut parts = vec![];
        for part in self.parts.drain(..).into_iter() {
            if let PathPart::FuncType(func_ty) = part {
                let s = func_ty.trim_matches(|ch| ch == '<' || ch == '>');
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
                parts.push(PathPart::FuncType(format!(
                    "<({}):{}>",
                    args.join(","),
                    ret
                )));
            } else if let PathPart::TypeArgs(args) = part {
                let args = args
                    .trim_matches(|ch| ch == '[' || ch == ']')
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
                let args = format!("[{}]", args.join(","));
                log::debug!("args: {}", args);
                parts.push(PathPart::TypeArgs(args));
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

        *self = Path { parts }
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        vec![]
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

    pub fn join<S: AsRef<str>>(&self, sep: S) -> String {
        self.parts
            .iter()
            .map(PathPart::to_string)
            .join(sep.as_ref())
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

    pub fn to_mangled(&self) -> String {
        let s = self
            .parts
            .iter()
            .map(|p| {
                let n = match p {
                    PathPart::Name(n) | PathPart::TypeArgs(n) | PathPart::FuncType(n) => n.clone(),
                };

                let mut n = n
                    .replace("$", "$u24")
                    .replace("::", "$CC")
                    .replace(":", "$u3a")
                    .replace(",", "$u2c")
                    .replace("<", "$LT")
                    .replace(">", "$GT")
                    .replace("(", "$LP")
                    .replace(")", "$RP")
                    .replace("[", "$LB")
                    .replace("]", "$RB");
                if !n.starts_with("$") {
                    n.insert(0, '$');
                }
                n
            })
            .collect::<Vec<_>>()
            .join("");

        format!("_ZN{}_{}E", s.len(), s)
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

    pub fn append_path<P: Into<Path>>(&self, p: P) -> Path {
        let mut parts = self.parts.clone();
        let other: Path = p.into();
        parts.extend(other.parts);
        Path { parts }
    }

    pub fn append_mut<T: ToString>(&mut self, s: T) {
        self.parts.push(PathPart::Name(s.to_string()));
    }

    pub fn append_func_type<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push(PathPart::FuncType(s.to_string()));
        Path { parts }
    }

    pub fn append_type_args<T: ToString>(&self, args: &[T]) -> Path {
        let mut parts = self.parts.clone();
        parts.push(PathPart::TypeArgs(format!(
            "[{}]",
            args.iter().map(|s| s.to_string()).join(",")
        )));
        Path { parts }
    }

    pub fn extend_mut<T: ToString, I: Iterator<Item = T>>(&mut self, i: I) {
        self.parts.extend(i.map(|s| PathPart::Name(s.to_string())));
    }

    pub fn merge(&self, rhs: &Path) -> Path {
        let mut parts = vec![];
        let mut idx = 0;
        while idx < self.parts.len() && idx < rhs.parts.len() {
            let lhs_part = &self.parts[idx];
            let rhs_part = &rhs.parts[idx];
            if lhs_part != rhs_part {
                break;
            }

            parts.push(lhs_part.clone());
            idx += 1;
        }

        parts.extend(
            self.parts
                .iter()
                .skip(idx)
                .cloned()
                .chain(rhs.parts.iter().skip(idx).cloned()),
        );
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

    pub fn without_func_type(&self) -> Path {
        let parts = self
            .parts
            .iter()
            .cloned()
            .filter(|p| !matches!(p, PathPart::FuncType(_)))
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
        write!(f, "{}", self.join("::"))
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.join("::"))
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
                Some(':') => self.maybe_finish_part(&mut chars),
                Some('<') => self.parse_func_type(&mut chars),
                Some('[') => self.parse_type_args(&mut chars),
                Some(ch) => self.curr_part.push(ch),
                _ => {
                    self.push_part();
                    break;
                }
            }
        }

        Path { parts: self.parts }
    }

    fn parse_func_type(&mut self, chars: &mut Chars) {
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

    fn parse_type_args(&mut self, chars: &mut Chars) {
        self.curr_part.push('[');
        loop {
            match chars.next() {
                Some(ch) if ch == '[' || ch == ']' || ch == ':' => {
                    self.curr_part.push(ch);
                    break;
                }
                Some(ch) => self.curr_part.push(ch),
                _ => break,
            }
        }
    }

    fn maybe_finish_part(&mut self, chars: &mut Chars) {
        match chars.next() {
            Some(':') | None => self.push_part(),
            Some(ch) => {
                self.curr_part.push(':');
                self.curr_part.push(ch);
            }
        }
    }

    fn push_part(&mut self) {
        let part = std::mem::take(&mut self.curr_part);
        let part = if part.starts_with('<') && part.ends_with('>') {
            PathPart::FuncType(part)
        } else if part.starts_with('[') && part.ends_with(']') {
            PathPart::TypeArgs(part)
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
