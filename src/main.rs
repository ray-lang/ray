#[macro_use]
mod macros;

mod ast;
mod cli;
mod codegen;
mod compiler;
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
mod sym;
mod target;
mod typing;
mod utils;

fn main() {
    cli::run();
}
