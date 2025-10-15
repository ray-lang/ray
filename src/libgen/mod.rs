use serde::{Deserialize, Serialize};

use crate::{
    ast::Path,
    lir,
    sema::NameContext,
    span::SourceMap,
    typing::{state::SchemeEnv, TyCtx},
};

#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub program: lir::Program,
    pub tcx: TyCtx,
    pub ncx: NameContext,
    pub srcmap: SourceMap,
    pub defs: SchemeEnv,
    pub modules: Vec<Path>,
}

pub fn serialize(
    program: lir::Program,
    tcx: TyCtx,
    ncx: NameContext,
    srcmap: SourceMap,
    defs: SchemeEnv,
    modules: Vec<Path>,
) -> Vec<u8> {
    bincode::serialize(&RayLib {
        program,
        tcx,
        ncx,
        srcmap,
        defs,
        modules,
    })
    .unwrap()
}
