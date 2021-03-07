#[macro_use]
mod macros;

mod anf;
mod ast;
mod cli;
mod codegen;
mod collections;
mod compiler;
mod convert;
mod cst;
mod driver;
mod errors;
mod graph;
mod hir;
mod lir;
mod parse;
mod pathlib;
mod sema;
mod sort;
mod span;
mod ssa;
mod strutils;
mod target;
mod typing;
mod utils;

fn main() {
    cli::run();
}
