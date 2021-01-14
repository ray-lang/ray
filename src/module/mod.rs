use std::collections::HashMap;

use crate::{ast::Module, pathlib::FilePath};

#[derive(Debug)]
pub struct ModuleMap {
    map: HashMap<FilePath, Module>,
}

impl ModuleMap {
    pub fn get(&mut self, fp: &FilePath) -> Option<&mut Module> {
        self.map.get_mut(fp)
    }

    pub fn add(&mut self, fp: &FilePath, m: Module) -> &mut Module {
        self.map.insert(fp.clone(), m);
        self.map.get_mut(fp).unwrap()
    }

    pub fn has(&self, fp: &FilePath) -> bool {
        self.map.contains_key(fp)
    }
}
