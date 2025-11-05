use std::{
    collections::{HashMap, HashSet},
    vec,
};

use serde::{Deserialize, Serialize};

use crate::ast::{Path, PathPart};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Scope {
    pub path: Path,
    pub names: Option<HashSet<String>>,
}

impl From<Vec<String>> for Scope {
    fn from(names: Vec<String>) -> Self {
        Self {
            path: Path::from(names),
            names: None,
        }
    }
}

impl From<&[&str]> for Scope {
    fn from(names: &[&str]) -> Self {
        Self {
            path: Path::from(names.iter().map(|s| s.to_string()).collect::<Vec<_>>()),
            names: None,
        }
    }
}

impl From<&[String]> for Scope {
    fn from(names: &[String]) -> Self {
        Self {
            path: Path::from(names),
            names: None,
        }
    }
}

impl From<Path> for Scope {
    fn from(path: Path) -> Self {
        Self { path, names: None }
    }
}

impl Scope {
    pub fn len(&self) -> usize {
        self.path.len()
    }

    pub fn is_empty(&self) -> bool {
        self.path.is_empty()
    }

    pub fn contains(&self, name: &String) -> bool {
        self.names
            .as_ref()
            .map(|names| names.contains(name))
            .unwrap_or(true)
    }

    pub fn pop(&mut self) -> PathPart {
        self.path.pop_back()
    }

    pub fn add_name(&mut self, name: String) {
        if self.names.is_none() {
            self.names = Some(HashSet::new());
        }

        self.names.as_mut().unwrap().insert(name);
    }

    pub fn split_first(&self) -> (String, Scope) {
        let mut path = self.path.clone();
        let name = path.pop_front().to_string();
        (
            name,
            Scope {
                path,
                names: self.names.clone(),
            },
        )
    }

    pub fn join<S: AsRef<str>>(&self, sep: S) -> String {
        self.path.join(sep)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NameTree {
    names: HashSet<String>,
    children: HashMap<String, Box<NameTree>>,
}

impl NameTree {
    pub fn new() -> Self {
        Self {
            names: HashSet::new(),
            children: HashMap::new(),
        }
    }

    pub fn extend(&mut self, other: NameTree) {
        log::debug!("extending name tree: {:?} and {:?}", self, other);
        self.names.extend(other.names);
        for (name, child) in other.children {
            if let Some(existing_child) = self.children.get_mut(&name) {
                existing_child.extend(*child);
            } else {
                self.children.insert(name, child);
            }
        }
    }

    pub fn add_name(&mut self, name: String) {
        self.names.insert(name);
    }

    pub fn add_full_name(&mut self, fqn: &[String]) {
        if fqn.len() == 0 {
            return;
        }

        let (name, scope) = fqn.split_last().unwrap();
        self.add_name_in_scope(scope, name.clone());
    }

    pub fn add_name_in_scope(&mut self, scope: &[String], name: String) {
        if scope.len() == 0 {
            self.names.insert(name);
            return;
        }

        let (first, scope) = scope.split_first().unwrap();
        if !self.children.contains_key(first) {
            self.children
                .insert(first.clone(), Box::new(NameTree::new()));
        }

        self.children
            .get_mut(first)
            .unwrap()
            .add_name_in_scope(scope, name);
    }

    pub fn find_names(&self, name: &str, scope: &[String]) -> Vec<Vec<String>> {
        let mut names = vec![];
        for other_name in self.names.iter() {
            if name == other_name {
                names.push(
                    scope
                        .iter()
                        .cloned()
                        .chain(vec![other_name.clone()])
                        .collect(),
                );
            }
        }

        for (key, child_tree) in self.children.iter() {
            let scope = scope
                .iter()
                .cloned()
                .chain(vec![key.clone()])
                .collect::<Vec<_>>();
            names.extend(child_tree.find_names(name, &scope));
        }

        names
    }

    pub fn find_scope(&self, scope: &Scope) -> Option<&NameTree> {
        if scope.is_empty() {
            return Some(self);
        }

        let (first, scope) = scope.split_first();
        if let Some(child) = self.children.get(&first) {
            return child.find_scope(&scope);
        }

        None
    }

    pub fn find_in_scope(&self, scope: &Scope, name: &String) -> bool {
        self.find_scope(scope)
            .map(|t| scope.contains(name) && t.names.contains(name))
            .unwrap_or_default()
    }

    fn find_from_parts(&self, scope: &Scope, parts: &[String]) -> Option<(Vec<String>, String)> {
        if parts.len() == 0 {
            return None;
        }

        if matches!(parts.first(), Some(part) if part == "super") {
            let mut scope = scope.clone();
            scope.pop();
            return self.find_from_parts(&scope, &parts[1..]);
        }

        let (name, child_scope) = parts.split_last().unwrap();
        let child_scope = Scope::from(child_scope);
        self.find_scope(scope)
            .and_then(|t| t.find_scope(&child_scope))
            .and_then(|t| {
                if !scope.contains(name) {
                    return None;
                }

                t.names.get(name)
            })
            .map(|name| {
                let mut path = scope.path.clone();
                path.append_mut(child_scope.path);
                (path.to_name_vec(), name.clone())
            })
    }

    pub fn find_in_scopes<'a>(&self, scopes: &'a [Scope], name: &String) -> Option<&'a Scope> {
        for scope in scopes.iter() {
            if self.find_in_scope(scope, &name) {
                return Some(scope);
            }
        }

        None
    }

    pub fn find_from_parts_in_scopes<'a>(
        &'a self,
        scopes: &'a [Scope],
        parts: &'a [String],
    ) -> Option<(Vec<String>, String)> {
        scopes
            .iter()
            .find_map(|scope| self.find_from_parts(scope, parts))
    }
}

#[cfg(test)]
mod nametree_test {
    use super::{NameTree, Scope};

    macro_rules! scope {
        ($($name:expr),*) => {
            Scope::from(&[$($name.to_string()),*][..])
        };
    }

    #[test]
    fn test_resolve() {
        let mut names = NameTree::new();
        names.add_name_in_scope(&[str!("core")], str!("print"));
        names.add_name_in_scope(&[str!("std"), str!("io")], str!("File"));

        let scopes = &[scope!("core"), scope!("std")];
        let name = str!("print");
        if let Some(scope) = names.find_in_scopes(scopes, &name) {
            println!("found name `{}` in scope: {}", name, scope.join("::"))
        } else {
            panic!("could not find name: {}", name);
        }

        let parts = &[str!("io"), str!("File")];
        if let Some((scope, name)) = names.find_from_parts_in_scopes(scopes, parts) {
            assert_eq!(scope.join("::"), "std::io");
            assert_eq!(name, "File");
            println!("found name `{}` in scope: {}", name, scope.join("::"),)
        } else {
            panic!("could not find name: {}", name);
        }
    }

    #[test]
    fn test_scoped_resolve() {
        let mut names = NameTree::new();
        names.add_name_in_scope(&[str!("std"), str!("io")], str!("File"));
        names.add_name_in_scope(&[str!("std"), str!("io")], str!("Result"));

        let mut scope = scope!("std", "io");
        scope.add_name(str!("File"));
        assert!(names.find_in_scope(&scope, &str!("File")));
        assert!(!names.find_in_scope(&scope, &str!("Result")));
    }
}
