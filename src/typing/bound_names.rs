// typing/bound_names.rs
use crate::ast::Path;
use crate::typing::ty::Ty;
use std::collections::HashMap;

#[derive(Default, Debug, Clone)]
pub struct BoundNames {
    // each frame is a lexical scope
    frames: Vec<HashMap<Path, Ty>>,
}

impl BoundNames {
    pub fn new() -> Self {
        Self {
            frames: vec![HashMap::new()],
        }
    }

    pub fn enter(&mut self) {
        self.frames.push(HashMap::new());
    }

    pub fn exit(&mut self) {
        self.frames.pop();
    }

    pub fn with_frame<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.enter();
        let result = f(self);
        self.exit();
        result
    }

    pub fn insert(&mut self, name: Path, ty: Ty) {
        if let Some(top) = self.frames.last_mut() {
            top.insert(name, ty);
        }
    }

    pub fn get(&self, name: &Path) -> Option<&Ty> {
        // search from innermost to outermost
        for frame in self.frames.iter().rev() {
            if let Some(t) = frame.get(name) {
                return Some(t);
            }
        }
        None
    }

    pub fn clear_to_one(&mut self) {
        self.frames.clear();
        self.frames.push(HashMap::new());
    }
}
