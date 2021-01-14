use crate::ast::Module;

use super::constraints::tree::ConstraintTree;

pub fn infer(module: &Module) {
    // let mut inf = Infer {
    //     constraints: ConstraintTree::empty(),
    // };

    // collect constraints from the module into a tree
    let ct = ConstraintTree::empty();
    // let cs = ct.flatten();
}
