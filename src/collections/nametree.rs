use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, PartialEq, Eq)]
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

    pub fn find_scope(&self, scope: &[String]) -> Option<&NameTree> {
        if scope.len() == 0 {
            return Some(self);
        }

        let (first, scope) = scope.split_first().unwrap();
        if let Some(child) = self.children.get(first) {
            return child.find_scope(scope);
        }

        None
    }

    pub fn find_in_scope(&self, scope: &[String], name: &String) -> bool {
        self.find_scope(scope)
            .map(|t| t.names.contains(name))
            .unwrap_or_default()
    }

    pub fn find_from_parts(&self, scope: &[String], parts: &[String]) -> bool {
        if parts.len() == 0 {
            return false;
        }

        let (name, child_scope) = parts.split_last().unwrap();
        self.find_scope(scope)
            .and_then(|t| t.find_scope(child_scope))
            .map(|t| t.names.contains(name))
            .unwrap_or_default()
    }

    pub fn find_in_scopes<'a>(
        &self,
        scopes: &'a [Vec<String>],
        name: &String,
    ) -> Option<&'a Vec<String>> {
        for i in scopes.iter() {
            let scope = i.as_slice();
            if self.find_in_scope(scope, &name) {
                return Some(i);
            }
        }

        None
    }

    pub fn find_from_parts_in_scopes<'a>(
        &self,
        scopes: &'a [Vec<String>],
        parts: &[String],
    ) -> Option<&'a Vec<String>> {
        for i in scopes.iter() {
            let scope = i.as_slice();
            if self.find_from_parts(scope, parts) {
                return Some(i);
            }
        }

        None
    }
}

#[cfg(test)]
mod nametree_test {
    use super::NameTree;

    #[test]
    fn test_resolve() {
        let mut names = NameTree::new();
        names.add_name_in_scope(&[str!("core")], str!("print"));
        names.add_name_in_scope(&[str!("std"), str!("io")], str!("File"));

        let scopes = &[vec![str!("core")], vec![str!("std")]];
        let name = str!("print");
        if let Some(scope) = names.find_in_scopes(scopes, &name) {
            println!("found name `{}` in scope: {}", name, scope.join("::"))
        } else {
            panic!("could not find name: {}", name);
        }

        let parts = &[str!("io"), str!("File")];
        if let Some(scope) = names.find_from_parts_in_scopes(scopes, parts) {
            println!(
                "found name `{}` in scope: {}",
                parts.join("::"),
                scope.join("::")
            )
        } else {
            panic!("could not find name: {}", name);
        }
    }
}
