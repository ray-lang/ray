#[macro_use]
mod macros;

mod ast;
mod cli;
mod codegen;
mod collections;
mod convert;
mod driver;
mod errors;
mod link;
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
