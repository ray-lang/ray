use std::{
    collections::{VecDeque, vec_deque::Drain},
    fmt,
    hash::Hasher,
    ops::RangeBounds,
    str::Chars,
};

use crate::{
    pathlib::FilePath,
    ty::{Ty, parser::TyParser},
    utils::join,
};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum PathPart {
    Name(String),
    TypeArgs(Vec<Ty>),
    Array(Ty, usize),
    FuncType(Vec<Ty>, Ty),
}

impl std::fmt::Debug for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) => write!(f, "{}", s),
            PathPart::TypeArgs(args) => write!(f, "[{}]", join(args, ",")),
            PathPart::Array(ty, size) => write!(f, "[{};{}]", ty, size),
            PathPart::FuncType(args, ret) => write!(f, "<({}):{}>", join(args, ","), ret),
        }
    }
}

impl std::fmt::Display for PathPart {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathPart::Name(s) => write!(f, "{}", s),
            PathPart::TypeArgs(args) => write!(f, "[{}]", join(args, ",")),
            PathPart::Array(ty, size) => write!(f, "[{};{}]", ty, size),
            PathPart::FuncType(args, ret) => write!(f, "<({}):{}>", join(args, ","), ret),
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

    pub fn root(&self) -> Option<Path> {
        self.parts.front().cloned().map(|part| {
            let mut parts = VecDeque::new();
            parts.push_back(part);
            Path { parts }
        })
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

    pub fn as_str(&self) -> &str {
        self.parts
            .back()
            .and_then(|part| match part {
                PathPart::Name(name) => Some(name.as_str()),
                _ => None,
            })
            .unwrap()
    }

    pub fn starts_with(&self, other: impl Into<Path>) -> bool {
        let other_path = other.into();
        if other_path.len() > self.len() {
            return false;
        }

        if other_path.len() == 0 {
            return true;
        }

        let mut i = 0;
        while i < self.len() && i < other_path.len() {
            if &self.parts[i] != &other_path.parts[i] {
                return false;
            }
            i += 1;
        }
        true
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

    pub fn to_filepath(&self) -> FilePath {
        let mut fp = FilePath::new();
        for p in self.parts.iter() {
            match p {
                PathPart::Name(s) if s == "super" => fp.push(".."),
                PathPart::Name(s) => fp.push(s),
                part => fp.push(part.to_string()),
            }
        }

        fp
    }

    pub fn to_mangled(&self) -> String {
        let s = self
            .parts
            .iter()
            .map(|p| {
                let n = match p {
                    PathPart::Name(n) => n.clone(),
                    p => p.to_string(),
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

    pub fn append_mut<T: ToString>(&mut self, s: T) -> &mut Self {
        self.parts.push_back(PathPart::Name(s.to_string()));
        self
    }

    pub fn append_func_type(&self, params: Vec<Ty>, ret: Ty) -> Path {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::FuncType(params, ret));
        Path { parts }
    }

    pub fn append_type_args<'a, I>(&self, args: I) -> Path
    where
        I: Iterator<Item = &'a Ty>,
    {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::TypeArgs(args.cloned().collect()));
        Path { parts }
    }

    pub fn append_array_type(&self, ty: Ty, size: usize) -> Path {
        let mut parts = self.parts.clone();
        parts.push_back(PathPart::Array(ty, size));
        Path { parts }
    }

    pub fn extend_mut<T: ToString, I: Iterator<Item = T>>(&mut self, i: I) {
        self.parts.extend(i.map(|s| PathPart::Name(s.to_string())));
    }

    pub fn drain<R>(&mut self, range: R) -> Drain<'_, PathPart>
    where
        R: RangeBounds<usize>,
    {
        self.parts.drain(range)
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

    pub fn to_short_name(&self) -> String {
        if let Some(name) = self.name() {
            name
        } else {
            self.to_string()
        }
    }

    pub fn without_func_type(&self) -> Path {
        let parts = self
            .parts
            .iter()
            .cloned()
            .filter(|p| !matches!(p, PathPart::FuncType(..)))
            .collect::<VecDeque<_>>();

        Path { parts }
    }

    pub fn parent(&self) -> Path {
        let mut parts = self.parts.clone();
        parts.pop_back();
        Path { parts }
    }

    pub fn iter(&self) -> impl Iterator<Item = &PathPart> {
        self.parts.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut PathPart> {
        self.parts.iter_mut()
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

impl From<VecDeque<PathPart>> for Path {
    fn from(parts: VecDeque<PathPart>) -> Path {
        Path { parts }
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

impl Into<String> for Path {
    fn into(self) -> String {
        self.to_string()
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
        if s.is_empty() {
            return Path {
                parts: VecDeque::new(),
            };
        }

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
        let mut depth = 0;
        loop {
            match chars.next() {
                Some(ch) if ch == '>' && depth == 0 => {
                    self.curr_part.push(ch);
                    break;
                }
                Some(ch) => {
                    match ch {
                        '<' => depth += 1,
                        '>' => depth -= 1,
                        _ => {}
                    }
                    self.curr_part.push(ch);
                }
                _ => break,
            }
        }
    }

    fn parse_type_args(&mut self, chars: &mut Chars) {
        self.curr_part.push('[');
        let mut depth = 0;
        loop {
            match chars.next() {
                Some(ch) if ch == ']' && depth == 0 => {
                    self.curr_part.push(ch);
                    break;
                }
                Some(ch) => {
                    match ch {
                        '[' => depth += 1,
                        ']' => depth -= 1,
                        _ => {}
                    }
                    self.curr_part.push(ch);
                }
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

    fn parse_part(&mut self) -> PathPart {
        let part = std::mem::take(&mut self.curr_part);
        if part.starts_with('<') && part.ends_with('>') {
            let mut ty_parser = TyParser::new(&part);
            ty_parser.expect("<");
            let Ty::Tuple(args) = ty_parser.parse_tuple_ty().unwrap() else {
                panic!("expected args in part {}", part);
            };
            ty_parser.expect(":");
            let ret_ty = ty_parser.parse_ty().unwrap();
            ty_parser.expect(">");
            PathPart::FuncType(args, ret_ty)
        } else if part.starts_with('[') && part.ends_with(']') {
            let mut ty_parser = TyParser::new(&part);
            ty_parser.expect("[");
            let mut tys = vec![];
            loop {
                let ty = ty_parser.parse_ty().unwrap();
                tys.push(ty);
                if let Some(']') = ty_parser.peek() {
                    break;
                }

                if let Some(';') = ty_parser.peek() {
                    ty_parser.expect(";").unwrap();
                    let num = ty_parser.parse_num();
                    return PathPart::Array(tys.pop().unwrap(), num);
                }

                ty_parser.expect(",");
            }
            ty_parser.expect("]");
            PathPart::TypeArgs(tys)
        } else {
            PathPart::Name(part)
        }
    }

    fn push_part(&mut self) {
        let part = self.parse_part();
        self.parts.push(part);
    }
}

#[macro_export]
macro_rules! path {
    ($($x:expr),*) => (Path::from(vec![$(String::from($x),)*]))
}

#[cfg(test)]
mod tests {
    use crate::{pathlib::path::PathParser, ty::Ty};

    use super::Path;

    #[test]
    fn test_canonicalize() {
        let path = path!("a", "b", "super", "c");
        assert_eq!(path.canonicalize(), path!("a", "c"));
    }

    #[test]
    fn test_starts_with() {
        let p1 = Path::from("a::b::c");
        let p2 = Path::from("a::b");
        assert!(p1.starts_with(&p2), "{} and {}", p1, p2);

        let p1 = Path::from("a");
        let p2 = Path::from("a");
        assert!(p1.starts_with(&p2), "{} and {}", p1, p2);

        let p1 = Path::from("a::b");
        let p2 = Path::from("a::b");
        assert!(p1.starts_with(&p2), "{} and {}", p1, p2);

        let p1 = Path::from("a");
        let p2 = Path::from("a::b");
        assert!(!p1.starts_with(&p2), "{} and {}", p1, p2);

        let p1 = Path::from("a::b");
        let p2 = Path::from("");
        assert!(p1.starts_with(&p2), "{} and {}", p1, p2);

        let p1 = Path::from("");
        let p2 = Path::from("a::b");
        assert!(!p1.starts_with(&p2), "{} and {}", p1, p2);
    }

    #[test]
    fn path_parser_basic_path() {
        let p1 = PathParser::new().parse("a::b".to_string());
        let mut p2 = Path::new();
        p2.append_mut("a").append_mut("b");
        assert_eq!(p1, p2);
    }

    #[test]
    fn path_parser_path_with_type_args() {
        let p1 = PathParser::new().parse("a::b::[i32, (pkg::A, pkg::B)]".to_string());
        let mut p2 = Path::new();
        p2.append_mut("a").append_mut("b");
        p2 = p2.append_type_args(
            vec![
                Ty::i32(),
                Ty::tuple(vec![Ty::con("pkg::A"), Ty::con("pkg::B")]),
            ]
            .iter(),
        );
        assert_eq!(p1, p2);
    }

    #[test]
    fn path_parser_path_with_array_args() {
        let p1 = PathParser::new().parse("core::array::[T; 32]".to_string());
        let mut p2 = Path::new();
        p2.append_mut("core").append_mut("array");
        p2 = p2.append_array_type(Ty::con("T"), 32);
        assert_eq!(p1, p2);
    }

    #[test]
    fn path_parser_path_with_inner_array_ty() {
        let p1 = PathParser::new().parse("pkg::T::[i32, (i8, [u8; 16])]".to_string());
        let mut p2 = Path::new();
        p2.append_mut("pkg").append_mut("T");
        p2 = p2.append_type_args(
            vec![
                Ty::i32(),
                Ty::tuple(vec![Ty::i8(), Ty::array(Ty::u8(), 16)]),
            ]
            .iter(),
        );
        assert_eq!(p1, p2);
    }
}
