use serde::{Deserialize, Serialize};

use crate::{
    lir,
    span::SourceMap,
    typing::{state::SchemeEnv, TyCtx},
};

#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub program: lir::Program,
    pub tcx: TyCtx,
    pub srcmap: SourceMap,
    pub defs: SchemeEnv,
}

pub fn serialize(program: lir::Program, tcx: TyCtx, srcmap: SourceMap, defs: SchemeEnv) -> Vec<u8> {
    bincode::serialize(&RayLib {
        program,
        tcx,
        srcmap,
        defs,
    })
    .unwrap()
}
