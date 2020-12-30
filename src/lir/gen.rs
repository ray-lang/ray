use crate::ast;
use crate::errors::{RayError, RayErrorKind, RayResult};
use crate::lir;
use crate::pathlib::FilePath;
use crate::sym;

use std::collections::HashMap;

pub fn gen() -> Result<lir::Program, RayError> {
    unimplemented!()
}

#[derive(Debug)]
struct GenCtx<'a> {
    fx: &'a mut lir::Func,
}

impl<'a> GenCtx<'a> {}

#[derive(Debug)]
struct Gen {
    fn_idx: HashMap<String, lir::Func>,
    module_cache: HashMap<String, sym::Symbol>,
}

impl Gen {
    pub fn compile_name(
        &self,
        n: ast::Name,
        ctx: &GenCtx,
    ) -> RayResult<(Vec<lir::Inst>, lir::Value)> {
        let ty = n.ty.as_ref().ok_or_else(|| RayError {
            fp: FilePath::new(),
            msg: format!(""),
            kind: RayErrorKind::Compile,
            span: Some(n.span),
        })?;

        unimplemented!()
    }
}
