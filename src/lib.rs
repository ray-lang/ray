#[macro_use]
extern crate lazy_static;

#[macro_use]
pub mod macros;

pub mod ast;
pub mod cli;
pub mod codegen;
pub mod collections;
pub mod convert;
pub mod driver;
pub mod errors;
pub mod libgen;
pub mod lir;
pub mod parse;
pub mod pathlib;
pub mod sema;
pub mod sort;
pub mod span;
pub mod strutils;
pub mod target;
pub mod transform;
pub mod typing;
pub mod utils;
