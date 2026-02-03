use std::collections::HashMap;

use ray_core::{ast::Node, sourcemap::SourceMap};
use ray_lir::{self as lir, SymbolSet};
use ray_shared::{optlevel::OptLevel, pathlib::Path};

pub mod llvm;

pub struct CodegenOptions {
    pub emit: bool,
    pub opt_level: OptLevel,
}

pub(self) fn collect_symbols(
    func: &lir::Func,
    symbols: &mut SymbolSet,
    fn_map: &HashMap<Path, &lir::Func>,
) {
    log::debug!("collecting symbols from func: {}", func.name);
    for sym in func.symbols.iter() {
        if !symbols.contains(sym) {
            log::debug!("adding symbol: {}", sym);
            symbols.insert(sym.clone());
            if let Some(func) = fn_map.get(sym) {
                collect_symbols(func, symbols, fn_map)
            } else {
                log::debug!("CANNOT FIND SYMBOL IN FN MAP: {}", sym);
            }
        }
    }
}

trait Codegen<Ctx> {
    type Output;

    fn codegen(&self, ctx: &mut Ctx, srcmap: &SourceMap) -> Self::Output;
}

impl<T, I, Ctx> Codegen<Ctx> for Vec<T>
where
    T: Codegen<Ctx, Output = I>,
{
    type Output = Vec<I>;

    fn codegen(&self, ctx: &mut Ctx, srcmap: &SourceMap) -> Self::Output {
        self.iter().map(|t| t.codegen(ctx, srcmap)).collect()
    }
}

impl<T, I, Ctx> Codegen<Ctx> for Node<T>
where
    T: Codegen<Ctx, Output = I>,
{
    type Output = I;

    fn codegen(&self, ctx: &mut Ctx, srcmap: &SourceMap) -> Self::Output {
        self.value.codegen(ctx, srcmap)
    }
}
