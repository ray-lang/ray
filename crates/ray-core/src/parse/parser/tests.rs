#![cfg(test)]

use super::{ParseDiagnostics, ParseOptions, Parser};
use crate::{
    ast::{Decl, Expr, FnParam, Func, InfixOp, Literal, Path, Pattern},
    errors::{RayError, RayErrorKind},
    pathlib::FilePath,
    span::SourceMap,
    typing::ty::{NominalKind, Ty},
};

#[allow(dead_code)]
fn enable_debug_logs() {
    fern::Dispatch::new()
        .level(log::LevelFilter::Debug)
        .chain(std::io::stderr())
        .apply()
        .unwrap();
}

fn test_options() -> ParseOptions {
    let mut options = ParseOptions::default();
    let filepath = FilePath::from("test.ray");
    options.filepath = filepath.clone();
    options.original_filepath = filepath;
    options.module_path = Path::from("test");
    options
}

fn parse_source(src: &str) -> (crate::ast::File, Vec<RayError>) {
    let mut srcmap = SourceMap::new();
    parse_source_with_srcmap(src, &mut srcmap)
}

fn parse_source_with_srcmap(
    src: &str,
    srcmap: &mut SourceMap,
) -> (crate::ast::File, Vec<RayError>) {
    let options = test_options();
    let ParseDiagnostics { value, errors } =
        Parser::parse_from_src_with_diagnostics(src, options, srcmap);
    let file = value.expect("expected successful parse despite recovery");
    (file, errors)
}

fn first_function(file: &crate::ast::File) -> &Func {
    match &file
        .decls
        .first()
        .expect("expected at least one declaration")
        .value
    {
        Decl::Func(func) => func,
        other => panic!("expected function declaration, got {:?}", other),
    }
}

fn function_body_block(func: &Func) -> &crate::ast::Block {
    let body = func.body.as_ref().expect("expected function body");
    match &body.value {
        Expr::Block(block) => block,
        other => panic!("expected function block expression, got {:?}", other),
    }
}

#[test]
fn parse_from_src_with_diagnostics_success() {
    let mut srcmap = SourceMap::new();
    let options = test_options();
    let result = Parser::parse_from_src_with_diagnostics("", options, &mut srcmap);

    assert!(result.value.is_some());
    assert!(result.errors.is_empty());
}

#[test]
fn parse_from_src_with_diagnostics_reports_parse_errors() {
    let mut srcmap = SourceMap::new();
    let options = test_options();
    let result = Parser::parse_from_src_with_diagnostics("fn main( {", options, &mut srcmap);

    assert!(
        result.value.is_some(),
        "expected partial parse even with errors"
    );
    assert!(!result.errors.is_empty());
    assert_eq!(result.errors[0].kind, RayErrorKind::UnexpectedToken);
    assert!(result.errors[0].src.first().and_then(|s| s.span).is_some());
}

#[test]
fn parse_from_src_with_diagnostics_preserves_doc_comment() {
    let mut srcmap = SourceMap::new();
    let options = test_options();
    let result = Parser::parse_from_src_with_diagnostics(
        "//! module documentation\nfn main() {}",
        options,
        &mut srcmap,
    );

    let file = result.value.expect("expected successful parse");
    assert_eq!(file.doc_comment.as_deref(), Some("module documentation"));
    assert!(result.errors.is_empty());
}

#[test]
fn parse_with_module_and_function_doc_comments() {
    let mut srcmap = SourceMap::new();
    let options = test_options();
    let source = r#"//! module docs
//! second line
//! extra spacing above is okay

/// function docs
/// more function docs
fn main() {
    mut x = 1
    x = 2
}
"#;
    let result = Parser::parse_from_src_with_diagnostics(source, options, &mut srcmap);
    assert!(
        result.errors.is_empty(),
        "expected no parse errors, got: {:?}",
        result.errors
    );
    let file = result.value.expect("expected successful parse");

    assert_eq!(
        file.doc_comment.as_deref(),
        Some("module docs\nsecond line\nextra spacing above is okay")
    );
    assert!(result.errors.is_empty());
    // Ensure at least one declaration collected the function doc comment via SourceMap.
    let decl = file.decls.first().expect("expected function declaration");
    let decl_doc = srcmap.doc(decl).expect("expected function doc comment");
    assert_eq!(decl_doc, "function docs\nmore function docs");
}

#[test]
fn parses_new_expression() {
    let src = r#"
fn main() {
    len = 10
    x = new(u8, len)
}
"#;

    let (_, errors) = parse_source(src);
    assert!(
        errors.is_empty(),
        "expected parsing without errors, got {:?}",
        errors
    );
}

#[test]
fn parses_box_expression() {
    let src = r#"
fn main() {
    x = 1
    y = box x
}
"#;

    let (_, errors) = parse_source(src);
    assert!(
        errors.is_empty(),
        "expected parsing without errors, got {:?}",
        errors
    );
}

#[test]
fn parses_ternary_expression() {
    let source = r#"
fn main() {
    x = 1 if true else 2
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected ternary expression to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts.first().expect("expected statement").value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };
    let rhs = assign.rhs.as_ref();
    let if_expr = match &rhs.value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected ternary if expression, got {:?}", other),
    };
    assert!(
        matches!(if_expr.then.value, Expr::Literal(_)),
        "expected literal then branch, got {:?}",
        if_expr.then.value
    );
    assert!(
        matches!(if_expr.cond.value, Expr::Literal(_)),
        "expected literal condition branch, got {:?}",
        if_expr.cond.value
    );
    assert!(
        matches!(
            if_expr.els.as_ref().map(|els| &els.value),
            Some(Expr::Literal(_))
        ),
        "expected literal else branch, got {:?}",
        if_expr.els.as_ref().map(|els| &els.value)
    );
}

#[test]
fn parses_ternary_precedence() {
    let source = r#"
fn main() {
    result = 1 + 2 if true else 3
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected ternary precedence expression to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts.first().expect("expected statement").value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };
    let binop = match &assign.rhs.as_ref().value {
        Expr::BinOp(binop) => binop,
        other => panic!("expected binary expression on RHS, got {:?}", other),
    };
    assert_eq!(
        binop.op.value,
        InfixOp::Add,
        "expected addition at the top level of the expression"
    );
    assert!(
        matches!(
            binop.lhs.as_ref().value,
            Expr::Literal(Literal::Integer { .. })
        ),
        "expected integer literal on the left-hand side of the addition, got {:?}",
        binop.lhs.as_ref().value
    );
    let if_expr = match &binop.rhs.as_ref().value {
        Expr::If(if_expr) => if_expr,
        other => panic!(
            "expected ternary expression on RHS of addition, got {:?}",
            other
        ),
    };
    assert!(
        matches!(if_expr.then.value, Expr::Literal(Literal::Integer { .. })),
        "expected literal then branch inside ternary, got {:?}",
        if_expr.then.value
    );
    assert!(
        matches!(if_expr.cond.value, Expr::Literal(Literal::Bool(true))),
        "expected literal condition, got {:?}",
        if_expr.cond.value
    );
    assert!(
        matches!(
            if_expr.els.as_ref().map(|els| &els.value),
            Some(Expr::Literal(Literal::Integer { .. }))
        ),
        "expected integer literal else branch, got {:?}",
        if_expr.els.as_ref().map(|els| &els.value)
    );
}

#[test]
fn parses_deref_assignment() {
    let src = r#"
fn main() {
    ptr = new(u8, 1)
    *ptr = 10
}
"#;
    let (file, errors) = parse_source(src);
    assert!(errors.is_empty(), "expected no errors, got {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 2,
        "expected 2 statements, found: {:#?}",
        block.stmts
    );

    let assign = block.stmts.get(0).expect("expected statement at [0]");
    if let Expr::Assign(assign) = &assign.value {
        assert!(
            matches!(assign.lhs.value, Pattern::Name(_)),
            "expected name on LHS, found: {:#?}",
            assign.lhs,
        );
    } else {
        panic!("expected assignment, found: {:#?}", assign,);
    }

    let deref_assign = block.stmts.get(1).expect("expected statement at [1]");
    if let Expr::Assign(assign) = &deref_assign.value {
        assert!(
            matches!(assign.lhs.value, Pattern::Deref(_)),
            "expected deref on LHS, found: {:#?}",
            assign.lhs,
        );
    } else {
        panic!("expected assignment, found: {:#?}", deref_assign,);
    }
}

#[test]
fn parses_derefs() {
    let src = r#"
fn main() {
    x = 1
    p = &x
    *p = 10
    y = *p + 1
}
"#;
    let (file, errors) = parse_source(src);
    assert!(errors.is_empty(), "expected no errors, got {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 4,
        "expected 4 statements, found: {:#?}",
        block.stmts
    );
}

#[test]
fn parses_if_after_stmt() {
    let src = r#"
fn main() {
    a = 1
    if a < 2 {}
}
"#;

    let (file, errors) = parse_source(src);
    assert!(errors.is_empty(), "expected no errors, got {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 2,
        "expected 2 statements, found: {:#?}",
        block.stmts
    );

    let assign = block.stmts.get(0).expect("expected statement at [0]");
    assert!(
        matches!(assign.value, Expr::Assign(_)),
        "expected assignment, found: {:#?}",
        assign,
    );

    let if_expr = block.stmts.get(1).expect("expected statement at [1]");
    assert!(
        matches!(if_expr.value, Expr::If(_)),
        "expected if expr, found {:#?}",
        if_expr,
    )
}

#[test]
fn parses_if_after_stmt_with_comment() {
    let src = r#"
fn main() {
    a = 1 // with comment
    if a < 2 {}
}
"#;

    let (file, errors) = parse_source(src);
    assert!(errors.is_empty(), "expected no errors, got {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 2,
        "expected 2 statements, found: {:#?}",
        block.stmts
    );

    let assign = block.stmts.get(0).expect("expected statement at [0]");
    assert!(
        matches!(assign.value, Expr::Assign(_)),
        "expected assignment, found: {:#?}",
        assign,
    );

    let if_expr = block.stmts.get(1).expect("expected statement at [1]");
    assert!(
        matches!(if_expr.value, Expr::If(_)),
        "expected if expr, found {:#?}",
        if_expr,
    )
}

#[test]
fn parses_if_after_stmt_with_semi() {
    let src = r#"
fn main() {
    a = 1; if a < 2 {}
}
"#;

    let (file, errors) = parse_source(src);
    assert!(errors.is_empty(), "expected no errors, got {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 2,
        "expected 2 statements, found: {:#?}",
        block.stmts
    );

    let assign = block.stmts.get(0).expect("expected statement at [0]");
    assert!(
        matches!(assign.value, Expr::Assign(_)),
        "expected assignment, found: {:#?}",
        assign,
    );

    let if_expr = block.stmts.get(1).expect("expected statement at [1]");
    assert!(
        matches!(if_expr.value, Expr::If(_)),
        "expected if expr, found {:#?}",
        if_expr,
    )
}

#[test]
fn parses_if_with_else_block() {
    let source = r#"
fn main() {
    if flag {
    } else {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected if-expression to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };
    match &if_expr.cond.value {
        Expr::Name(name) => assert_eq!(name.path.to_string(), "flag"),
        other => panic!("expected condition name `flag`, got {:?}", other),
    }
    match &if_expr.then.value {
        Expr::Block(body) => assert!(
            body.stmts.is_empty(),
            "expected empty then block in this test"
        ),
        other => panic!("expected block in then branch, got {:?}", other),
    }
    match if_expr
        .els
        .as_ref()
        .map(|els| &els.value)
        .expect("expected else branch")
    {
        Expr::Block(body) => assert!(
            body.stmts.is_empty(),
            "expected empty else block in this test"
        ),
        other => panic!("expected block in else branch, got {:?}", other),
    }
}

#[test]
fn parses_if_with_block_condition() {
    let source = r#"
fn main() {
    if { true } {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected block condition to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };
    match &if_expr.cond.value {
        Expr::Block(cond_block) => assert!(
            cond_block.stmts.len() == 1,
            "expected condition block to contain single literal expression"
        ),
        other => panic!("expected block expression condition, got {:?}", other),
    }
    match &if_expr.then.value {
        Expr::Block(body) => assert!(body.stmts.is_empty(), "expected then block to be empty"),
        other => panic!("expected block in then branch, got {:?}", other),
    }
    assert!(
        if_expr.els.is_none(),
        "did not expect else branch in this test"
    );
}

#[test]
fn recovers_missing_field_type() {
    let source = r#"
struct Foo { field:, }
"#;
    let (file, errors) = parse_source(source);
    assert!(!errors.is_empty(), "expected errors for missing field type");
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    assert_eq!(fields.len(), 1, "expected single field");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected placeholder type on field")
        .clone_value();
    let ty = ty_scheme.into_mono();
    assert!(matches!(ty, Ty::Never), "expected Ty::Never placeholder");
}

#[test]
fn recovers_missing_return_type() {
    let source = r#"
fn main() -> {
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing return type"
    );
    let func = first_function(&file);
    let ty = func
        .sig
        .ret_ty
        .as_ref()
        .expect("expected placeholder return type")
        .clone_value();
    assert!(matches!(ty, Ty::Never), "expected Ty::Never placeholder");
}

#[test]
fn recovers_missing_cast_type() {
    let source = r#"
fn main() {
    1 as;
}
"#;
    let (file, errors) = parse_source(source);
    assert!(!errors.is_empty(), "expected errors for missing cast type");
    let func = first_function(&file);
    let block = function_body_block(func);
    let cast = match &block.stmts.first().expect("expected statement").value {
        Expr::Cast(cast) => cast,
        other => panic!("expected cast expression, got {:?}", other),
    };
    let ty = cast.ty.clone_value();
    assert!(matches!(ty, Ty::Never), "expected Ty::Never placeholder");
}

#[test]
fn recovers_missing_array_element_type() {
    let source = r#"
struct Foo {
    field: [; 3],
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing array element type"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    let ty = ty_scheme.into_mono();
    match ty {
        Ty::Array(elem, size) => {
            assert_eq!(size, 3, "expected element count to remain intact");
            assert!(
                matches!(*elem, Ty::Never),
                "expected element placeholder to be Ty::Never"
            );
        }
        other => panic!("expected array placeholder, got {:?}", other),
    }
}

#[test]
fn recovers_malformed_array_size_literal() {
    let source = r#"
struct Foo {
    field: [i32; what],
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for malformed array size literal"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    let ty = ty_scheme.into_mono();
    assert!(
        matches!(ty, Ty::Never),
        "expected Ty::Never placeholder for malformed array"
    );
}

#[test]
fn recovers_tuple_type_element() {
    let source = r#"
struct Foo {
    tuple: (i32, , bool),
}
"#;
    let (file, errors) = parse_source(source);
    assert!(!errors.is_empty(), "expected errors for tuple type element");
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    let ty = ty_scheme.into_mono();
    match ty {
        Ty::Tuple(tys) => {
            assert_eq!(tys.len(), 3, "expected three tuple elements");
            assert!(
                matches!(tys[1], Ty::Never),
                "expected placeholder in missing tuple slot"
            );
        }
        other => panic!("expected tuple type, got {:?}", other),
    }
}

#[test]
fn recovers_missing_where_qualifier() {
    let source = r#"
fn main() where {
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing where qualifier"
    );
    let func = first_function(&file);
    assert_eq!(
        func.sig.qualifiers.len(),
        1,
        "expected placeholder qualifier entry"
    );
    let ty = func.sig.qualifiers[0].clone_value();
    assert!(
        matches!(ty, Ty::Never),
        "expected Ty::Never placeholder for missing qualifier"
    );
}

#[test]
fn recovers_missing_fn_type_return() {
    let source = r#"
struct Foo {
    cb: Fn(i32) -> ,
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing function return type"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    let ty = ty_scheme.into_mono();
    match ty {
        Ty::Func(_, ret) => {
            assert!(
                matches!(*ret, Ty::Never),
                "expected Ty::Never placeholder for missing return type"
            );
        }
        other => panic!("expected function type, got {:?}", other),
    }
}

#[test]
fn recovers_missing_union_member() {
    let source = r#"
struct Foo {
    field: A | ,
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing union member"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    match ty_scheme.into_mono() {
        Ty::Union(tys) => {
            assert_eq!(tys.len(), 2, "expected two union members");
            assert!(
                matches!(tys[1], Ty::Never),
                "expected Ty::Never placeholder for missing member"
            );
        }
        other => panic!("expected union type, got {:?}", other),
    }
}

#[test]
fn recovers_missing_union_middle_member() {
    let source = r#"
struct Foo {
    field: A | | B,
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing union member"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    match ty_scheme.into_mono() {
        Ty::Union(tys) => {
            assert_eq!(tys.len(), 3, "expected three union members");
            assert!(
                matches!(tys[1], Ty::Never),
                "expected missing member to be Ty::Never"
            );
        }
        other => panic!("expected union type, got {:?}", other),
    }
}

#[test]
fn recovers_missing_union_in_parens() {
    let source = r#"
struct Foo {
    field: (A | ),
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for missing union member inside parens"
    );
    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    let fields = st.fields.expect("expected fields on struct");
    let field = &fields[0];
    let ty_scheme = field
        .value
        .ty
        .as_ref()
        .expect("expected type placeholder on field")
        .clone_value();
    match ty_scheme.into_mono() {
        Ty::Union(tys) => {
            assert_eq!(tys.len(), 2, "expected two union elements");
            assert!(
                matches!(tys[1], Ty::Never),
                "expected missing member to be Ty::Never"
            );
        }
        other => panic!("expected union type, got {:?}", other),
    }
}

#[test]
fn recovers_missing_union_at_eof() {
    let source = r#"
struct Foo {
    field: A | 
"#;
    let (_file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected errors for dangling union member at EOF"
    );
}
#[test]
fn parses_for_loop_expression() {
    let source = r#"
fn main() {
    for item in items {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected for-loop to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let for_expr = match &block.stmts.first().expect("expected statement").value {
        Expr::For(for_expr) => for_expr,
        other => panic!("expected for expression, got {:?}", other),
    };
    match &for_expr.pat.value {
        Pattern::Name(name) => assert_eq!(name.path.to_string(), "item"),
        other => panic!("expected pattern `item`, got {:?}", other),
    }
    match for_expr.expr.as_ref().value {
        Expr::Name(ref name) => assert_eq!(name.path.to_string(), "items"),
        ref other => panic!("expected iterable name `items`, got {:?}", other),
    }
    match for_expr.body.as_ref().value {
        Expr::Block(ref body) => assert!(
            body.stmts.is_empty(),
            "expected loop body block to be empty"
        ),
        ref other => panic!("expected block body for for-loop, got {:?}", other),
    }
}

#[test]
fn parses_while_loop_expression() {
    let source = r#"
fn main() {
    while has_items {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected while-loop to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let while_expr = match &block.stmts.first().expect("expected statement").value {
        Expr::While(while_expr) => while_expr,
        other => panic!("expected while expression, got {:?}", other),
    };
    match while_expr.cond.as_ref().value {
        Expr::Name(ref name) => assert_eq!(name.path.to_string(), "has_items"),
        ref other => panic!("expected condition name `has_items`, got {:?}", other),
    }
    match while_expr.body.as_ref().value {
        Expr::Block(ref body) => {
            assert!(body.stmts.is_empty(), "expected while body to be empty")
        }
        ref other => panic!("expected block body for while-loop, got {:?}", other),
    }
}

#[test]
fn parses_loop_expression() {
    let source = r#"
fn main() {
    loop {
        break
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected loop expression to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let loop_expr = match &block.stmts.first().expect("expected statement").value {
        Expr::Loop(loop_expr) => loop_expr,
        other => panic!("expected loop expression, got {:?}", other),
    };
    match &loop_expr.body.as_ref().value {
        Expr::Block(body) => {
            assert_eq!(
                body.stmts.len(),
                1,
                "expected loop body to contain a single statement"
            );
            match &body.stmts[0].value {
                Expr::Break(_) => {}
                other => panic!("expected break statement in loop body, got {:?}", other),
            }
        }
        other => panic!("expected block body for loop expression, got {:?}", other),
    }
}

#[test]
fn parses_chained_ternary_expression() {
    let source = r#"
fn main() {
    result = 0 if a else 1 if b else 2
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        errors.is_empty(),
        "expected chained ternary to parse without errors, got: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts.first().expect("expected statement").value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };
    let outer_if = match &assign.rhs.as_ref().value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected outer ternary expression, got {:?}", other),
    };
    let inner_if = match outer_if
        .els
        .as_ref()
        .map(|els| &els.value)
        .expect("expected nested ternary in else branch")
    {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected nested ternary expression, got {:?}", other),
    };
    assert!(
        matches!(outer_if.then.value, Expr::Literal(Literal::Integer { .. })),
        "expected literal in outer then branch, got {:?}",
        outer_if.then.value
    );
    assert!(
        matches!(outer_if.cond.value, Expr::Name(_)),
        "expected name in outer condition, got {:?}",
        outer_if.cond.value
    );
    assert!(
        matches!(inner_if.then.value, Expr::Literal(Literal::Integer { .. })),
        "expected literal in inner then branch, got {:?}",
        inner_if.then.value
    );
    assert!(
        matches!(inner_if.cond.value, Expr::Name(_)),
        "expected name in inner condition, got {:?}",
        inner_if.cond.value
    );
    assert!(
        matches!(
            inner_if.els.as_ref().map(|els| &els.value),
            Some(Expr::Literal(Literal::Integer { .. }))
        ),
        "expected literal in inner else branch, got {:?}",
        inner_if.els.as_ref().map(|els| &els.value)
    );
}

#[test]
fn parses_curly_expression() {
    let src = r#"
fn main() {
    len = 10
    raw_ptr = new(u8, len)
    s = string { raw_ptr, len }
}
"#;
    let mut srcmap = SourceMap::new();
    let (file, errors) = parse_source_with_srcmap(src, &mut srcmap);
    assert!(
        errors.is_empty(),
        "expected parse without errors, got {:?}",
        errors
    );

    let func = first_function(&file);
    let block = function_body_block(func);

    assert!(
        block.stmts.len() == 3,
        "expected 3 statements, found {}",
        block.stmts.len()
    );

    let assign = match &block.stmts[2].value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };

    let curly = match &assign.rhs.value {
        Expr::Curly(curly) => curly,
        other => panic!("expected curly expression, got {:?}", other),
    };

    // check elements
    let raw_ptr_elem = &curly.elements[0];
    let raw_ptr_elem_src = srcmap.get(raw_ptr_elem);
    let raw_ptr_elem_span = raw_ptr_elem_src.span.expect("expected span");
    assert!(raw_ptr_elem_span.start.lineno == 4);
    assert!(raw_ptr_elem_span.end.lineno == 4);
}

#[test]
fn parses_oneline_struct() {
    let src = r#"
struct T { x: u32, y: u32 }
"#;
    let (file, errors) = parse_source(src);
    assert!(
        errors.is_empty(),
        "expected trait to parse without errors, got: {:?}",
        errors
    );

    let decl = file
        .decls
        .first()
        .expect("expected struct declaration")
        .value
        .clone();
    let st = match decl {
        Decl::Struct(st) => st,
        other => panic!("expected struct declaration, got {:?}", other),
    };
    assert_eq!(st.kind, NominalKind::Struct);
    assert_eq!(st.path.to_string(), "test::T");
}

#[test]
fn parses_trait() {
    let src = r#"
trait Printable {
    fn print(self: 'a)
}
"#;
    let (file, errors) = parse_source(src);
    assert!(
        errors.is_empty(),
        "expected trait to parse without errors, got: {:?}",
        errors
    );
    let decl = file
        .decls
        .first()
        .expect("expected trait declaration")
        .value
        .clone();
    let tr = match decl {
        Decl::Trait(tr) => tr,
        other => panic!("expected trait declaration, got {:?}", other),
    };
    assert_eq!(tr.path.to_string(), "test::Printable");
    assert_eq!(
        tr.fields.len(),
        1,
        "expected single item in trait declaration"
    );
    let field = &tr.fields[0];
    match &field.value {
        Decl::FnSig(func_sig) => {
            assert_eq!(func_sig.path.to_string(), "test::Printable::print");
            assert_eq!(
                func_sig.params.len(),
                1,
                "expected single parameter in trait function"
            );
            match &func_sig.params[0].value {
                FnParam::Name(name) => assert_eq!(name.path.to_string(), "self"),
                other => panic!("expected parameter pattern `self`, got {:?}", other),
            }
        }
        other => panic!("expected function item in trait, got {:?}", other),
    }
}

#[test]
fn recovers_missing_ternary_condition() {
    let source = r#"
fn main() {
    result = 1 if else 2
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors when ternary condition is missing"
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts.first().expect("expected statement").value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };
    let if_expr = match &assign.rhs.as_ref().value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected ternary expression on RHS, got {:?}", other),
    };
    match &if_expr.cond.value {
        Expr::Missing(missing) => assert_eq!(
            missing.expected, "expression",
            "expected missing expression placeholder for ternary condition"
        ),
        other => panic!("expected missing condition expression, got {:?}", other),
    }
    assert!(
        matches!(if_expr.then.value, Expr::Literal(Literal::Integer { .. })),
        "expected literal then branch, got {:?}",
        if_expr.then.value
    );

    assert!(if_expr.els.is_some(), "expected else branch to be present");
    let else_value = if_expr
        .els
        .as_ref()
        .map(|els| &els.value)
        .expect("expected else");
    assert!(
        matches!(else_value, Expr::Literal(Literal::Integer { .. })),
        "expected literal else branch, got {:?}",
        else_value,
    );
}

#[test]
fn recovers_if_with_incomplete_condition() {
    let source = r#"
fn main() {
    if (
    {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for incomplete if condition"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected if statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };
    match &if_expr.cond.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder condition expression"
            );
        }
        other => panic!("expected missing condition expression, got {:?}", other),
    }
}

#[test]
fn recovers_if_without_block() {
    let source = r#"
fn main() {
    if true
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing if block"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected if statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };
    match &if_expr.then.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder expression"
            );
        }
        other => panic!("expected missing expression, got {:?}", other),
    }
}

#[test]
fn recovers_if_without_condition_or_block() {
    let src = r#"
fn main() {
    if
}
"#;

    let (file, errors) = parse_source(src);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing if condition and block"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );

    // debug print errors
    eprintln!("Parse errors: {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected if statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };

    let missing = match &if_expr.cond.value {
        Expr::Missing(missing) => missing,
        other => panic!("expected missing if condition, got {:?}", other),
    };

    assert_eq!(
        missing.expected, "expression",
        "expected placeholder missing expression"
    );
}

#[test]
fn recovers_if_else_without_condition_or_blocks() {
    let src = r#"
fn main() {
    if
    else
}
"#;
    let (file, errors) = parse_source(src);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing if condition and blocks"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );

    // debug print errors
    eprintln!("Parse errors: {:#?}", errors);

    let func = first_function(&file);
    let block = function_body_block(func);
    let if_expr = match &block.stmts.first().expect("expected if statement").value {
        Expr::If(if_expr) => if_expr,
        other => panic!("expected if expression, got {:?}", other),
    };

    let missing_cond = match &if_expr.cond.value {
        Expr::Missing(missing) => missing,
        other => panic!("expected missing if condition, got {:?}", other),
    };

    assert_eq!(
        missing_cond.expected, "expression",
        "expected placeholder missing expression for condition"
    );

    let missing_then = match &if_expr.then.value {
        Expr::Missing(missing) => missing,
        other => panic!("expected missing then block, got {:?}", other),
    };

    assert_eq!(
        missing_then.expected, "expression",
        "expected placeholder missing for then branch"
    );
}

#[test]
fn recovers_for_without_pattern() {
    let source = r#"
fn main() {
    for in [1] {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing for pattern"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let for_expr = match &block.stmts.first().expect("expected for statement").value {
        Expr::For(for_expr) => for_expr,
        other => panic!("expected for expression, got {:?}", other),
    };
    let missing = match &for_expr.pat.value {
        Pattern::Missing(missing) => missing,
        other => panic!("expected missing pattern, got {:?}", other),
    };
    assert_eq!(
        missing.expected, "pattern",
        "expected placeholder missing pattern"
    );
}

#[test]
fn recovers_for_without_iterable() {
    let source = r#"
fn main() {
    for x in
    {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing for iterable"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let for_expr = match &block.stmts.first().expect("expected for statement").value {
        Expr::For(for_expr) => for_expr,
        other => panic!("expected for expression, got {:?}", other),
    };
    match &for_expr.expr.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder iterable expression"
            );
        }
        other => panic!("expected missing iterable expression, got {:?}", other),
    }
}

#[test]
fn recovers_for_without_body() {
    let source = r#"
fn main() {
    for x in [1]
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing for body"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let for_expr = match &block.stmts.first().expect("expected for statement").value {
        Expr::For(for_expr) => for_expr,
        other => panic!("expected for expression, got {:?}", other),
    };
    match &for_expr.body.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder empty for body"
            );
        }
        other => panic!("expected missing expression, got {:?}", other),
    }
}

#[test]
fn recovers_while_with_incomplete_condition() {
    let source = r#"
fn main() {
    while (
    {
    }
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for incomplete while condition"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let while_expr = match &block.stmts.first().expect("expected while statement").value {
        Expr::While(while_expr) => while_expr,
        other => panic!("expected while expression, got {:?}", other),
    };
    match &while_expr.cond.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder condition expression"
            );
        }
        other => panic!("expected missing condition expression, got {:?}", other),
    }
}

#[test]
fn recovers_while_without_body() {
    let source = r#"
fn main() {
    while true
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing while body"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let while_expr = match &block.stmts.first().expect("expected while statement").value {
        Expr::While(while_expr) => while_expr,
        other => panic!("expected while expression, got {:?}", other),
    };
    match &while_expr.body.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder empty while body"
            );
        }
        other => panic!("expected missing expression, got {:?}", other),
    }
}

#[test]
fn recovers_loop_without_body() {
    let source = r#"
fn main() {
    loop
}
"#;
    let (file, errors) = parse_source(source);
    assert!(
        !errors.is_empty(),
        "expected parse errors for missing loop body"
    );
    assert!(
        !file.decls.is_empty(),
        "expected function declaration, errors: {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let loop_expr = match &block.stmts.first().expect("expected loop statement").value {
        Expr::Loop(loop_expr) => loop_expr,
        other => panic!("expected loop expression, got {:?}", other),
    };
    match &loop_expr.body.value {
        Expr::Missing(missing) => {
            assert_eq!(
                missing.expected, "expression",
                "expected placeholder empty loop body"
            );
        }
        other => panic!("expected missing expression, got {:?}", other),
    }
}

#[test]
fn statement_recovery_advances_block() {
    let src = r#"
fn main() {
    x =
    y = 2
}
"#;
    let (file, errors) = parse_source(src);
    assert_eq!(
        errors.len(),
        1,
        "expected single parse error, got {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    assert_eq!(
        block.stmts.len(),
        2,
        "expected two statements after recovery"
    );
    let assign = match &block.stmts[0].value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment with missing RHS, got {:?}", other),
    };
    assert!(
        matches!(assign.rhs.value, Expr::Missing(_)),
        "expected missing RHS after recovery, got {:?}",
        assign.rhs.value
    );
    assert!(
        matches!(block.stmts[1].value, Expr::Assign(_)),
        "expected second statement to remain an assignment, got {:?}",
        block.stmts[1].value
    );
}

#[test]
fn sequence_recovery_inserts_missing_element() {
    let src = r#"
fn main() {
    arr = [1, , 3]
}
"#;
    let (file, errors) = parse_source(src);
    assert_eq!(
        errors.len(),
        1,
        "expected single parse error, got {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts[0].value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment statement, got {:?}", other),
    };
    let list = match &assign.rhs.value {
        Expr::List(list) => list,
        other => panic!("expected list expression, got {:?}", other),
    };
    assert_eq!(list.items.len(), 3);
    assert!(matches!(list.items[0].value, Expr::Literal(_)));
    assert!(matches!(list.items[1].value, Expr::Missing(_)));
    assert!(matches!(list.items[2].value, Expr::Literal(_)));
}

#[test]
fn nested_error_leaves_closers_intact() {
    let src = r#"
fn main() {
    foo(1, { x = ; }, 3)
}
"#;
    let (file, errors) = parse_source(src);
    assert_eq!(
        errors.len(),
        1,
        "expected single parse error, got {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let call = match &block.stmts[0].value {
        Expr::Call(call) => call,
        other => panic!("expected call expression, got {:?}", other),
    };
    assert_eq!(
        call.args.items.len(),
        3,
        "expected three arguments after recovery"
    );
    assert!(matches!(call.args.items[0].value, Expr::Literal(_)));
    assert!(matches!(call.args.items[2].value, Expr::Literal(_)));
}

#[test]
fn expression_recovery_inserts_missing_rhs() {
    let src = r#"
fn main() {
    x = 1 +
}
"#;
    let (file, errors) = parse_source(src);
    assert_eq!(
        errors.len(),
        1,
        "expected single parse error, got {:?}",
        errors
    );
    let func = first_function(&file);
    let block = function_body_block(func);
    let assign = match &block.stmts[0].value {
        Expr::Assign(assign) => assign,
        other => panic!("expected assignment, got {:?}", other),
    };
    let binop = match &assign.rhs.value {
        Expr::BinOp(bin) => bin,
        other => panic!("expected binary operation, got {:?}", other),
    };
    assert_eq!(binop.op.value, InfixOp::Add);
    assert!(
        matches!(binop.rhs.value, Expr::Missing(_)),
        "expected missing RHS"
    );
}

#[test]
fn decorator_newline_optional_for_fn() {
    let src = r#"
@inline fn add(a: int, b: int) -> int {
    a + b
}
"#;
    let mut srcmap = SourceMap::new();
    let (file, errors) = parse_source_with_srcmap(src, &mut srcmap);
    assert!(
        errors.is_empty(),
        "expected parsing decorated inline fn without newline to succeed, got {:?}",
        errors
    );
    let decl = file.decls.first().expect("expected function declaration");
    let decorators = srcmap
        .get_decorators(decl)
        .expect("expected decorator metadata on fn");
    assert_eq!(decorators.len(), 1);
    assert_eq!(decorators[0].path.value, Path::from("inline"));
}

#[test]
fn decorator_newline_optional_for_extern_fn() {
    let src = r#"
@intrinsic extern fn add(a: int, b: int) -> int
"#;
    let mut srcmap = SourceMap::new();
    let (file, errors) = parse_source_with_srcmap(src, &mut srcmap);
    assert!(
        errors.is_empty(),
        "expected parsing inline-decorated extern fn without newline to succeed, got {:?}",
        errors
    );
    let decl = file.decls.first().expect("expected extern function declaration");
    let decorators = srcmap
        .get_decorators(decl)
        .expect("expected decorator metadata on extern fn");
    assert_eq!(decorators.len(), 1);
    assert_eq!(decorators[0].path.value, Path::from("intrinsic"));
}
