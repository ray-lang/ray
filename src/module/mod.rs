use crate::ast::Module;
use crate::pathlib::FilePath;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

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
