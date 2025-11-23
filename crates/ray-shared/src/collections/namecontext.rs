use serde::{Deserialize, Serialize};

use crate::{
    collections::nametree::{NameTree, Scope},
    pathlib::Path,
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NameContext {
    nametree: NameTree,
}

impl NameContext {
    pub fn new() -> Self {
        Self {
            nametree: NameTree::new(),
        }
    }

    pub fn nametree(&self) -> &NameTree {
        &self.nametree
    }

    pub fn nametree_mut(&mut self) -> &mut NameTree {
        &mut self.nametree
    }

    pub fn extend(&mut self, ncx: NameContext) {
        self.nametree.extend(ncx.nametree);
    }

    pub fn resolve_name(&self, scopes: &[Scope], name: &String) -> Option<Path> {
        log::debug!("resolving name `{}` in scopes: {:?}", name, scopes);
        self.nametree.find_in_scopes(scopes, name).map(|scope| {
            log::debug!("found scope {:?} for name `{}`", scope, name);
            let mut parts = scope.path.clone();
            parts.append_mut(name);
            parts
        })
    }

    pub fn resolve_path(&self, scopes: &[Scope], path: &Path) -> Option<Path> {
        log::debug!("[resolve_path] scopes={:?}, path={}", scopes, path);
        let parts = path.to_name_vec();
        log::debug!("[resolve_path] parts={:?}", parts);
        self.nametree
            .find_from_parts_in_scopes(scopes, &parts)
            .map(|(scope, name)| {
                let mut path = Path::from(&scope);
                path.append_mut(&name);
                log::debug!(
                    "[resolve_path] found name={} in scope={:?} => {}",
                    name,
                    scope,
                    path
                );
                path
            })
    }

    pub fn builtin_trait(&self, name: &str) -> Path {
        match &self.nametree().find_names(name, &[]).as_slice() {
            &[parts] => Path::from(parts),
            _ => Path::from(format!("core::{}", name)),
        }
    }
}
