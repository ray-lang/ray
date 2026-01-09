use crate::ast::LowerAST;

#[macro_use]
extern crate lazy_static;

#[macro_use]
pub mod macros;

pub mod ast;
pub mod codegen;
pub mod convert;
pub mod errors;
pub mod ide;
pub mod libgen;
pub mod lir;
pub mod parse;
pub mod passes;
pub mod sema;
pub mod sort;
pub mod sourcemap;
pub mod strutils;
pub mod target;
pub mod transform;
pub mod typing;
