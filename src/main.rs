#[macro_use]
mod macros;

mod ast;
mod cli;
mod codegen;
mod collections;
mod compiler;
mod convert;
mod cst;
mod driver;
mod errors;
mod hir;
mod lir;
mod parse;
mod pathlib;
mod sema;
mod sort;
mod span;
mod strutils;
mod target;
mod typing;
mod utils;

fn main() {
    cli::run();
}
