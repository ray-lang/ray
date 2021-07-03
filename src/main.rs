#[macro_use]
mod macros;

mod ast;
mod cli;
mod codegen;
mod collections;
mod convert;
mod driver;
mod errors;
mod libgen;
mod lir;
mod parse;
mod pathlib;
mod sema;
mod sort;
mod span;
mod strutils;
mod target;
mod transform;
mod typing;
mod utils;

fn main() {
    cli::run();
}
