use std::collections::{HashMap, HashSet};

use lir::SymbolSet;

use crate::{
    ast::{Node, Path},
    lir,
    span::SourceMap,
    typing::{ty::Ty, TyCtx},
};

pub mod llvm;
pub mod wasm;

pub(self) fn collect_symbols(
    func: &lir::Func,
    symbols: &mut SymbolSet,
    fn_map: &HashMap<Path, &Node<lir::Func>>,
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

trait CodegenCtx {
    type GenTy;
    type Func;
    type FuncBody;

    fn global(&mut self, name: &str) -> u32;

    fn add_global(
        &mut self,
        name: String,
        init_value: i32,
        ty: Self::GenTy,
        is_mutable: bool,
    ) -> u32;

    fn type_of(&self, var: &lir::Variable) -> &Ty;

    fn get_type_ref(&mut self, param_tys: &Vec<Ty>, ret_ty: &Ty) -> u32;

    fn add_func_name(&mut self, idx: u32, name: &Path);

    fn add_func(&mut self, name: &Path, func: Self::Func, body: Self::FuncBody) -> u32;

    fn add_func_import(&mut self, name: Path);

    fn get_body(&mut self, name: &Path) -> &mut Self::FuncBody;
}

trait GetLocals {
    fn get_locals(&self) -> HashSet<u32>;
}

trait Codegen<Ctx>
where
    Ctx: CodegenCtx,
{
    type Output;

    fn codegen(&self, ctx: &mut Ctx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output;
}

impl<T, I, Ctx> Codegen<Ctx> for Vec<T>
where
    Ctx: CodegenCtx,
    T: Codegen<Ctx, Output = I>,
{
    type Output = Vec<I>;

    fn codegen(&self, ctx: &mut Ctx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        self.iter().map(|t| t.codegen(ctx, tcx, srcmap)).collect()
    }
}

impl<T, I, Ctx> Codegen<Ctx> for Node<T>
where
    T: Codegen<Ctx, Output = I>,
    Ctx: CodegenCtx,
{
    type Output = I;

    fn codegen(&self, ctx: &mut Ctx, tcx: &TyCtx, srcmap: &SourceMap) -> Self::Output {
        self.value.codegen(ctx, tcx, srcmap)
    }
}
