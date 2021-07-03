use serde::{Deserialize, Serialize};

use crate::{
    lir,
    span::SourceMap,
    typing::{state::TyEnv, TyCtx},
};

#[derive(Debug, Serialize, Deserialize)]
pub struct RayLib {
    pub program: lir::Program,
    pub tcx: TyCtx,
    pub srcmap: SourceMap,
    pub defs: TyEnv,
}

pub fn serialize(program: lir::Program, tcx: TyCtx, srcmap: SourceMap, defs: TyEnv) -> Vec<u8> {
    bincode::serialize(&RayLib {
        program,
        tcx,
        srcmap,
        defs,
    })
    .unwrap()
}
