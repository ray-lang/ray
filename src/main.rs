#[macro_use]
mod macros;

mod anf;
mod ast;
mod cli;
mod codegen;
mod collections;
mod compiler;
mod convert;
mod driver;
mod errors;
mod graph;
mod link;
mod lir;
mod parse;
mod pathlib;
mod scf;
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
