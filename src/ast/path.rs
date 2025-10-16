use std::{collections::VecDeque, fmt, hash::Hasher, str::Chars};

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use top::{Subst, Substitutable};

use crate::{
    pathlib::FilePath,
    typing::ty::{Ty, TyVar},
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PathPart {
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

impl PathPart {
    fn as_str(&self) -> &str {
        match self {
            PathPart::Name(s) | PathPart::TypeArgs(s) | PathPart::FuncType(s) => s,
        }
    }
}

#[derive(Clone, Eq, Default, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Path {
    parts: VecDeque<PathPart>,
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
        let mut parts = VecDeque::new();
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
                parts.push_back(PathPart::FuncType(format!(
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
                parts.push_back(PathPart::TypeArgs(args));
            } else {
                parts.push_back(part);
                let tv = TyVar(Path {
                    parts: parts.clone(),
                });
                if let Some(ty) = subst.get(&tv) {
                    parts = ty
                        .to_string()
                        .split("::")
                        .map(|s| PathPart::Name(s.to_string()))
                        .collect::<VecDeque<_>>();
                }
            }
        }

        *self = Path { parts }
    }

    fn apply_subst_all(&mut self, subst: &Subst<TyVar, Ty>) {
        self.apply_subst(subst);
    }

    fn free_vars(&self) -> Vec<&TyVar> {
        vec![]
    }
}

impl Path {
    pub fn new() -> Path {
        Path {
            parts: VecDeque::new(),
        }
    }

    pub fn name(&self) -> Option<String> {
        self.parts.back().map(PathPart::to_string)
    }

    pub fn len(&self) -> usize {
        self.parts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.parts.is_empty()
    }

    pub fn is_relative(&self) -> bool {
        self.parts.iter().any(|p| match p {
            PathPart::Name(s) => s == "super",
            _ => false,
        })
    }

    pub fn is_self(&self) -> bool {
        self.name().unwrap().as_str() == "self"
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

    pub fn to_vec(&self) -> Vec<&str> {
        self.parts.iter().map(|p| p.as_str()).collect()
    }

    pub fn to_filepath(&self) -> FilePath {
        let mut fp = FilePath::new();
        for p in self.parts.iter() {
            match p {
                PathPart::Name(s) if s == "super" => fp.push(".."),
                PathPart::Name(s) | PathPart::TypeArgs(s) | PathPart::FuncType(s) => fp.push(s),
            }
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
        parts.push_back(PathPart::Name(String::from("*")));
        Path { parts }
    }

    pub fn append<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::Name(s.to_string()));
        Path { parts }
    }

    pub fn append_path<P: Into<Path>>(&self, p: P) -> Path {
        let mut parts = self.parts.clone();
        let other: Path = p.into();
        parts.extend(other.parts);
        Path { parts }
    }

    pub fn append_mut<T: ToString>(&mut self, s: T) {
        self.parts.push_back(PathPart::Name(s.to_string()));
    }

    pub fn append_func_type<T: ToString>(&self, s: T) -> Path {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::FuncType(s.to_string()));
        Path { parts }
    }

    pub fn append_type_args<T: ToString>(&self, args: &[T]) -> Path {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::TypeArgs(format!(
            "[{}]",
            args.iter().map(|s| s.to_string()).join(",")
        )));
        Path { parts }
    }

    pub fn extend_mut<T: ToString, I: Iterator<Item = T>>(&mut self, i: I) {
        self.parts.extend(i.map(|s| PathPart::Name(s.to_string())));
    }

    pub fn merge(&self, rhs: &Path) -> Path {
        let mut parts = VecDeque::new();
        let mut idx = 0;
        while idx < self.parts.len() && idx < rhs.parts.len() {
            let lhs_part = &self.parts[idx];
            let rhs_part = &rhs.parts[idx];
            if lhs_part != rhs_part {
                break;
            }

            parts.push_back(lhs_part.clone());
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

    pub fn pop_front(&mut self) -> PathPart {
        self.parts.pop_front().unwrap()
    }

    pub fn pop_back(&mut self) -> PathPart {
        self.parts.pop_back().unwrap()
    }

    pub fn canonicalize(&self) -> Path {
        let mut parts = self.parts.clone();
        let mut idx = 0;
        while idx < parts.len() {
            let part = &parts[idx];
            match part {
                PathPart::Name(name) if name == "super" => {
                    // remove the previous index and current index
                    parts.remove(idx);
                    parts.remove(idx - 1);
                    idx -= 1;
                }
                _ => {
                    idx += 1;
                }
            }
        }
        Path { parts }
    }

    pub fn root_from_filepath(&self, filepath: &FilePath) -> Path {
        let parts = self
            .parts
            .iter()
            .rev()
            .zip(filepath.split().iter().rev())
            .filter_map(|(a, b)| match a {
                PathPart::Name(name) if name == b => None,
                _ => Some(a.clone()),
            })
            .rev()
            .collect();

        Path { parts }
    }

    pub fn resolve_from_parent(&self, parent: &Path) -> (Path, Path) {
        let mut parent_parts = parent.parts.clone();
        let mut parts = VecDeque::new();
        for part in &self.parts {
            match part {
                PathPart::Name(s) if s == "super" => {
                    parent_parts.pop_back();
                }
                _ => parts.push_back(part.clone()),
            }
        }

        (
            Path {
                parts: parent_parts,
            },
            Path { parts },
        )
    }

    pub fn without_parent(&self, parent: &Path) -> Path {
        let mut idx = 0;
        while idx < self.parts.len() && idx < parent.parts.len() {
            let part = &self.parts[idx];
            let parent_part = &parent.parts[idx];
            if parent_part != part {
                break;
            }

            idx += 1;
        }

        let parts = self.parts.iter().skip(idx).cloned().collect();
        Path { parts }
    }

    pub fn with_name<T: ToString>(&self, name: T) -> Path {
        let mut parts = self.parts.clone();
        let name = PathPart::Name(name.to_string());
        if let Some(last) = parts.back_mut() {
            *last = name;
        } else {
            parts = VecDeque::from([name]);
        }
        Path { parts }
    }

    pub fn with_names_only(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.retain(|p| match p {
            PathPart::Name(_) => true,
            _ => false,
        });
        Path { parts }
    }

    pub fn without_type_args(&self) -> Path {
        let parts = self
            .parts
            .iter()
            .filter(|part| !matches!(part, PathPart::TypeArgs(_)))
            .cloned()
            .collect();
        Path { parts }
    }

    pub fn to_name_vec(&self) -> Vec<String> {
        self.parts
            .iter()
            .filter_map(|p| match p {
                PathPart::Name(s) => Some(s.clone()),
                _ => None,
            })
            .collect()
    }

    pub fn without_func_type(&self) -> Path {
        let parts = self
            .parts
            .iter()
            .cloned()
            .filter(|p| !matches!(p, PathPart::FuncType(_)))
            .collect::<VecDeque<_>>();

        Path { parts }
    }

    pub fn parent(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.pop_back();
        Path { parts }
    }

    // pub fn split_name(&self) -> (&[PathPart], &PathPart) {
    //     let (last, rest) = self.parts.split_back().unwrap();
    //     (rest, last)
    // }
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
            parts: VecDeque::from([PathPart::Name(f.file_stem())]),
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

impl From<&[String]> for Path {
    fn from(parts: &[String]) -> Path {
        Path {
            parts: parts.iter().cloned().map(PathPart::Name).collect(),
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

        Path {
            parts: VecDeque::from(self.parts),
        }
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

#[cfg(test)]
mod test_path {
    use super::Path;

    #[test]
    fn test_canonicalize() {
        let path = path!("a", "b", "super", "c");
        assert_eq!(path.canonicalize(), path!("a", "c"));
    }
}
