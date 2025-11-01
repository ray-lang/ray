use crate::{
    ast::{
        self, Assign, Curly, CurlyElement, Decl, Expr, FnParam, Func, FuncSig, Import, ImportKind,
        Name, Node, Pattern, Struct, Trait,
    },
    parse::{ParseDiagnostics, ParseOptions, Parser},
    pathlib::FilePath,
    span::{Pos, SourceMap, Span, TriviaKind, parsed::Parsed},
    typing::ty::{Ty, TyScheme},
};

/// A coarse-grained set of semantic token kinds. These intentionally mirror the
/// token categories exposed by the Language Server Protocol, but the list can
/// grow over time as the highlighter matures.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenKind {
    Type,
    Trait,
    Function,
    Variable,
    Parameter,
    Field,
    String,
    Operator,
    Namespace,
    Keyword,
    Comment,
    Number,
}

/// Modifiers that decorate a semantic token (e.g. declaration vs. usage).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenModifier {
    Declaration,
    Definition,
    Mutable,
}

/// Result of the semantic walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticToken {
    pub span: Span,
    pub kind: SemanticTokenKind,
    pub modifiers: Vec<SemanticTokenModifier>,
}

impl SemanticToken {
    pub fn new(span: Span, kind: SemanticTokenKind) -> Self {
        Self {
            span,
            kind,
            modifiers: Vec::new(),
        }
    }

    pub fn with_modifiers(mut self, modifiers: &[SemanticTokenModifier]) -> Self {
        self.modifiers.extend_from_slice(modifiers);
        self
    }
}

/// Public entry-point used by IDE-facing features.
pub fn collect(file: &ast::File, srcmap: &SourceMap) -> Vec<SemanticToken> {
    let mut tokens = SemanticTokenCollector::collect(file, srcmap);
    append_trivia_tokens(&mut tokens, srcmap);
    sort_tokens(&mut tokens);
    tokens
}

/// Parses `source` into an AST and collects semantic tokens. This is a
/// convenience wrapper for IDE consumers that do not already have an AST handy.
pub fn collect_from_source(source: &str) -> Vec<SemanticToken> {
    let mut srcmap = SourceMap::new();
    let mut options = ParseOptions::default();
    let filepath = FilePath::from("memory:semantic_tokens.ray");
    options.filepath = filepath.clone();
    options.original_filepath = filepath;
    options.module_path = ast::Path::from("semantic_tokens");

    let ParseDiagnostics { value, .. } =
        Parser::parse_from_src_with_diagnostics(source, options, &mut srcmap);

    let Some(file) = value else {
        return Vec::new();
    };

    let mut tokens = SemanticTokenCollector::collect_with_source(&file, &srcmap, Some(source));
    append_trivia_tokens(&mut tokens, &srcmap);
    sort_tokens(&mut tokens);

    tokens
}

struct SemanticTokenCollector<'a> {
    srcmap: &'a SourceMap,
    source: Option<&'a str>,
    tokens: Vec<SemanticToken>,
}

impl<'a> SemanticTokenCollector<'a> {
    fn collect(file: &'a ast::File, srcmap: &'a SourceMap) -> Vec<SemanticToken> {
        Self::collect_with_source(file, srcmap, None)
    }

    fn collect_with_source(
        file: &'a ast::File,
        srcmap: &'a SourceMap,
        source: Option<&'a str>,
    ) -> Vec<SemanticToken> {
        let mut collector = SemanticTokenCollector {
            srcmap,
            source,
            tokens: Vec::new(),
        };
        collector.visit_file(file);
        collector.tokens
    }

    fn visit_file(&mut self, file: &ast::File) {
        for import in &file.imports {
            self.visit_import(import);
        }

        for decl in &file.decls {
            self.visit_decl(decl);
        }

        for stmt in &file.stmts {
            self.visit_expr(stmt);
        }
    }

    fn visit_import(&mut self, import: &Import) {
        match &import.kind {
            ImportKind::Path(path) => self.emit_path_node(path, SemanticTokenKind::Namespace, &[]),
            ImportKind::Names(path, names) => {
                self.emit_path_node(path, SemanticTokenKind::Namespace, &[]);
                for name in names {
                    self.emit_path_node(name, SemanticTokenKind::Namespace, &[]);
                }
            }
            ImportKind::CImport(_, span) => {
                self.emit_span(*span, SemanticTokenKind::String, &[]);
            }
        }
    }

    fn visit_decl(&mut self, decl: &Node<Decl>) {
        match &decl.value {
            Decl::Struct(strct) => self.visit_struct(strct),
            Decl::Trait(tr) => self.visit_trait(tr),
            Decl::Func(func) => {
                self.visit_func(func);
            }
            Decl::FnSig(sig) => self.visit_fn_sig(sig, &[SemanticTokenModifier::Declaration]),
            Decl::TypeAlias(name, ty) => {
                self.emit_name_node(
                    name,
                    SemanticTokenKind::Type,
                    &[SemanticTokenModifier::Declaration],
                );
                self.emit_parsed_ty(ty, SemanticTokenKind::Type);
            }
            Decl::Impl(im) => self.visit_impl(im),
            Decl::Extern(ext) => self.visit_decl(ext.decl_node()),
            Decl::Mutable(name) => {
                self.emit_name_node(
                    name,
                    SemanticTokenKind::Variable,
                    &[
                        SemanticTokenModifier::Declaration,
                        SemanticTokenModifier::Mutable,
                    ],
                );
            }
            Decl::Name(name) => {
                self.emit_name_node(
                    name,
                    SemanticTokenKind::Variable,
                    &[SemanticTokenModifier::Declaration],
                );
            }
            Decl::Declare(assign) => self.visit_assign(assign),
        }
    }

    fn visit_struct(&mut self, strct: &Struct) {
        self.emit_path_node(
            &strct.path,
            SemanticTokenKind::Type,
            &[SemanticTokenModifier::Declaration],
        );

        if let Some(params) = &strct.ty_params {
            for ty in &params.tys {
                self.emit_parsed_ty(ty, SemanticTokenKind::Type);
            }
        }

        if let Some(fields) = &strct.fields {
            for field in fields {
                self.emit_name_node(
                    field,
                    SemanticTokenKind::Field,
                    &[SemanticTokenModifier::Declaration],
                );
                if let Some(ty) = &field.value.ty {
                    self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
                }
            }
        }
    }

    fn visit_trait(&mut self, tr: &Trait) {
        self.emit_parsed_ty(&tr.ty, SemanticTokenKind::Trait);
        if let Some(super_trait) = &tr.super_trait {
            self.emit_parsed_ty(super_trait, SemanticTokenKind::Trait);
        }
        for decl in &tr.fields {
            self.visit_decl(decl);
        }
        for directive in &tr.directives {
            if let Some(span) = directive.span().copied() {
                self.emit_span(span, SemanticTokenKind::Keyword, &[]);
            }
            for arg in &directive.args {
                self.emit_parsed_ty(arg, SemanticTokenKind::Type);
            }
        }
    }

    fn visit_impl(&mut self, im: &ast::Impl) {
        self.emit_parsed_ty(&im.ty, SemanticTokenKind::Type);
        for qualifier in &im.qualifiers {
            self.emit_parsed_ty(qualifier, SemanticTokenKind::Type);
        }
        if let Some(externs) = &im.externs {
            for decl in externs {
                self.visit_decl(decl);
            }
        }
        if let Some(funcs) = &im.funcs {
            for func in funcs {
                self.visit_func(func);
            }
        }
        if let Some(consts) = &im.consts {
            for assign in consts {
                self.visit_assign(assign);
            }
        }
    }

    fn visit_func(&mut self, func: &Func) {
        self.visit_fn_sig(&func.sig, &[SemanticTokenModifier::Definition]);
        if let Some(body) = &func.body {
            self.visit_expr(body);
        }
    }

    fn visit_fn_sig(&mut self, sig: &FuncSig, modifiers: &[SemanticTokenModifier]) {
        if let Some(span) = self.function_name_span(sig) {
            self.emit_span(span, SemanticTokenKind::Function, modifiers);
        } else if sig.span.len() != 0 {
            self.emit_span(sig.span, SemanticTokenKind::Function, modifiers);
        }

        if let Some(params) = &sig.ty_params {
            for ty in &params.tys {
                self.emit_parsed_ty(ty, SemanticTokenKind::Type);
            }
        }

        for param in &sig.params {
            self.visit_fn_param(param);
        }

        if let Some(ret_ty) = &sig.ret_ty {
            self.emit_parsed_ty(ret_ty, SemanticTokenKind::Type);
        }

        for qualifier in &sig.qualifiers {
            self.emit_parsed_ty(qualifier, SemanticTokenKind::Type);
        }
    }

    fn visit_fn_param(&mut self, param: &Node<FnParam>) {
        match &param.value {
            FnParam::Name(name) => {
                let span = self.srcmap.span_of(param);
                self.emit_span(
                    span,
                    SemanticTokenKind::Parameter,
                    &[SemanticTokenModifier::Declaration],
                );
                if let Some(ty) = &name.ty {
                    self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
                }
            }
            FnParam::DefaultValue(inner, expr) => {
                self.visit_fn_param(inner);
                self.visit_expr(expr);
            }
            FnParam::Missing { .. } => {}
        }
    }

    fn visit_assign(&mut self, assign: &Assign) {
        self.visit_pattern(&assign.lhs);
        self.visit_expr(&assign.rhs);
        self.emit_span(assign.op_span, SemanticTokenKind::Operator, &[]);
    }

    fn visit_pattern(&mut self, pattern: &Node<Pattern>) {
        match &pattern.value {
            Pattern::Name(name) | Pattern::Deref(Node { id: _, value: name }) => {
                let span = self.srcmap.span_of(pattern);
                self.emit_span(
                    span,
                    SemanticTokenKind::Variable,
                    &[SemanticTokenModifier::Declaration],
                );
                if let Some(ty) = &name.ty {
                    self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
                }
            }
            Pattern::Sequence(seq) | Pattern::Tuple(seq) => {
                for pat in seq {
                    self.visit_pattern(pat);
                }
            }
            Pattern::Missing(_) => {}
        }
    }

    fn visit_expr(&mut self, expr: &Node<Expr>) {
        match &expr.value {
            Expr::Assign(assign) => self.visit_assign(assign),
            Expr::Asm(_) => {}
            Expr::BinOp(binop) => {
                self.visit_expr(&binop.lhs);
                self.visit_expr(&binop.rhs);
                self.emit_span(
                    self.srcmap.span_of(&binop.op),
                    SemanticTokenKind::Operator,
                    &[],
                );
            }
            Expr::Block(block) => {
                for stmt in &block.stmts {
                    self.visit_expr(stmt);
                }
            }
            Expr::Boxed(boxed) => self.visit_expr(&boxed.inner),
            Expr::Break(value) => {
                if let Some(expr) = value {
                    self.visit_expr(expr);
                }
            }
            Expr::Return(value) => {
                if let Some(expr) = value {
                    self.visit_expr(expr);
                }
            }
            Expr::Call(call) => {
                if let Expr::Name(name) = &call.callee.value {
                    let span = self.srcmap.span_of(&call.callee);
                    self.emit_name(name, span, SemanticTokenKind::Function, &[]);
                } else {
                    self.visit_expr(&call.callee);
                }

                for arg in &call.args.items {
                    self.visit_expr(arg);
                }
            }
            Expr::Cast(cast) => {
                self.visit_expr(&cast.lhs);
                self.emit_parsed_ty(&cast.ty, SemanticTokenKind::Type);
            }
            Expr::Closure(closure) => {
                for arg in &closure.args.items {
                    self.visit_expr(arg);
                }
                self.visit_expr(&closure.body);
            }
            Expr::Curly(curly) => self.visit_curly(curly),
            Expr::Deref(deref) => {
                self.emit_span(deref.op_span, SemanticTokenKind::Operator, &[]);
                self.visit_expr(&deref.expr);
            }
            Expr::DefaultValue(expr) => self.visit_expr(expr),
            Expr::Dot(dot) => {
                self.visit_expr(&dot.lhs);
                self.emit_name_node(&dot.rhs, SemanticTokenKind::Field, &[]);
            }
            Expr::Func(func) => self.visit_func(func),
            Expr::For(for_loop) => {
                self.visit_pattern(&for_loop.pat);
                self.visit_expr(&for_loop.expr);
                self.visit_expr(&for_loop.body);
            }
            Expr::If(if_expr) => {
                self.visit_expr(&if_expr.cond);
                self.visit_expr(&if_expr.then);
                if let Some(els) = &if_expr.els {
                    self.visit_expr(els);
                }
            }
            Expr::Index(index) => {
                self.visit_expr(&index.lhs);
                self.visit_expr(&index.index);
            }
            Expr::Labeled(label, value) => {
                self.visit_expr(label);
                self.visit_expr(value);
            }
            Expr::List(list) => {
                for item in &list.items {
                    self.visit_expr(item);
                }
            }
            Expr::Literal(lit) => {
                let kind = match lit {
                    ast::Literal::Integer { .. }
                    | ast::Literal::Float { .. }
                    | ast::Literal::Bool(_) => SemanticTokenKind::Number,
                    ast::Literal::String(_)
                    | ast::Literal::ByteString(_)
                    | ast::Literal::Byte(_)
                    | ast::Literal::Char(_)
                    | ast::Literal::UnicodeEscSeq(_) => SemanticTokenKind::String,
                    ast::Literal::Nil => SemanticTokenKind::Keyword,
                    ast::Literal::Unit => return,
                };

                let span = self.srcmap.span_of(expr);
                self.emit_span(span, kind, &[]);
            }
            Expr::Loop(loop_expr) => self.visit_expr(&loop_expr.body),
            Expr::Missing(_) => {}
            Expr::Name(name) => {
                let span = self.srcmap.span_of(expr);
                self.emit_name(name, span, SemanticTokenKind::Variable, &[]);
            }
            Expr::New(new_expr) => {
                self.emit_node_parsed_ty(&new_expr.ty, SemanticTokenKind::Type);
                if let Some(count) = &new_expr.count {
                    self.visit_expr(count);
                }
            }
            Expr::Path(_) => {
                let span = self.srcmap.span_of(expr);
                self.emit_span(span, SemanticTokenKind::Namespace, &[]);
            }
            Expr::Pattern(_) => {}
            Expr::Paren(inner) => self.visit_expr(inner),
            Expr::Range(range) => {
                self.visit_expr(&range.start);
                self.visit_expr(&range.end);
                self.emit_span(range.op_span, SemanticTokenKind::Operator, &[]);
            }
            Expr::Ref(rf) => {
                self.emit_span(rf.op_span, SemanticTokenKind::Operator, &[]);
                self.visit_expr(&rf.expr);
            }
            Expr::Sequence(seq) => {
                for item in &seq.items {
                    self.visit_expr(item);
                }
            }
            Expr::Tuple(tuple) => {
                for item in &tuple.seq.items {
                    self.visit_expr(item);
                }
            }
            Expr::Type(scheme) => self.emit_parsed_tyscheme(scheme, SemanticTokenKind::Type),
            Expr::TypeAnnotated(value, ty) => {
                self.visit_expr(value);
                self.emit_parsed_tyscheme(&ty.value, SemanticTokenKind::Type);
            }
            Expr::UnaryOp(unary) => {
                self.emit_span(
                    self.srcmap.span_of(&unary.op),
                    SemanticTokenKind::Operator,
                    &[],
                );
                self.visit_expr(&unary.expr);
            }
            Expr::Unsafe(body) => self.visit_expr(body),
            Expr::While(while_loop) => {
                self.visit_expr(&while_loop.cond);
                self.visit_expr(&while_loop.body);
            }
        }
    }

    fn visit_curly(&mut self, curly: &Curly) {
        if let Some(lhs) = &curly.lhs {
            let kind = if matches!(lhs.name(), Some(n) if Ty::is_builtin_name(&n)) {
                SemanticTokenKind::Keyword
            } else {
                SemanticTokenKind::Type
            };
            self.emit_parsed_path(lhs, kind);
        }

        for element in &curly.elements {
            match &element.value {
                CurlyElement::Name(name) => {
                    let span = self.srcmap.span_of(element);
                    self.emit_span(span, SemanticTokenKind::Field, &[]);
                    if let Some(ty) = &name.ty {
                        self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
                    }
                }
                CurlyElement::Labeled(name, expr) => {
                    let span = self.srcmap.span_of(element);
                    self.emit_span(
                        span,
                        SemanticTokenKind::Field,
                        &[SemanticTokenModifier::Declaration],
                    );
                    if let Some(ty) = &name.ty {
                        self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
                    }
                    self.visit_expr(expr);
                }
            }
        }
    }

    fn emit_name(
        &mut self,
        name: &Name,
        span: Span,
        kind: SemanticTokenKind,
        modifiers: &[SemanticTokenModifier],
    ) {
        let kind = if let Some(name) = name.path.name()
            && name == "self"
        {
            SemanticTokenKind::Keyword
        } else {
            kind
        };
        self.emit_span(span, kind, modifiers);
        if let Some(ty) = &name.ty {
            self.emit_parsed_tyscheme(ty, SemanticTokenKind::Type);
        }
    }

    fn emit_name_node(
        &mut self,
        name: &Node<Name>,
        kind: SemanticTokenKind,
        modifiers: &[SemanticTokenModifier],
    ) {
        let span = self.srcmap.span_of(name);
        self.emit_name(name, span, kind, modifiers);
    }

    fn emit_path_node(
        &mut self,
        path: &Node<ast::Path>,
        kind: SemanticTokenKind,
        modifiers: &[SemanticTokenModifier],
    ) {
        let span = self.srcmap.span_of(path);
        self.emit_span(span, kind, modifiers);
    }

    fn emit_parsed_tyscheme(&mut self, scheme: &Parsed<TyScheme>, kind: SemanticTokenKind) {
        if let Some(span) = scheme.span().copied() {
            if matches!(scheme.value().mono(), Ty::Never) {
                return;
            }
            let kind = if scheme.value().mono().is_builtin() {
                SemanticTokenKind::Keyword
            } else {
                kind
            };

            self.emit_span(span, kind, &[]);
        }
    }

    fn emit_parsed_ty(&mut self, ty: &Parsed<Ty>, kind: SemanticTokenKind) {
        if let Some(span) = ty.span().copied() {
            if matches!(ty.value(), Ty::Never) {
                return;
            }

            let kind = if ty.is_builtin() {
                SemanticTokenKind::Keyword
            } else {
                kind
            };
            self.emit_span(span, kind, &[]);
        }
    }

    fn emit_node_parsed_ty(&mut self, node: &Node<Parsed<Ty>>, kind: SemanticTokenKind) {
        if let Some(span) = node.value.span().copied() {
            if matches!(node.value.value(), Ty::Never) {
                return;
            }
            self.emit_span(span, kind, &[]);
        }
    }

    fn emit_parsed_path(&mut self, path: &Parsed<ast::Path>, kind: SemanticTokenKind) {
        if let Some(span) = path.span().copied() {
            self.emit_span(span, kind, &[]);
        }
    }

    fn function_name_span(&self, sig: &FuncSig) -> Option<Span> {
        if sig.is_anon {
            return None;
        }

        let source = self.source?;
        let name = sig.path.name()?;
        if name.is_empty() || sig.span.len() == 0 {
            return None;
        }

        let start_offset = sig.span.start.offset.min(source.len());
        let end_offset = sig.span.end.offset.min(source.len());
        if start_offset >= end_offset {
            return None;
        }

        let slice = &source[start_offset..end_offset];
        let rel_start = slice.find(&name)?;
        let name_start = start_offset + rel_start;
        let name_end = name_start + name.len();

        let prefix = &source[start_offset..name_start];
        let name_text = &source[name_start..name_end];

        let start_pos = advance_pos(sig.span.start, prefix);
        let end_pos = advance_pos(start_pos, name_text);

        Some(Span {
            start: start_pos,
            end: end_pos,
        })
    }

    fn emit_span(
        &mut self,
        span: Span,
        kind: SemanticTokenKind,
        modifiers: &[SemanticTokenModifier],
    ) {
        if span.len() == 0 {
            return;
        }
        let token = SemanticToken::new(span, kind).with_modifiers(modifiers);
        self.tokens.push(token);
    }
}

fn advance_pos(mut pos: Pos, text: &str) -> Pos {
    for ch in text.chars() {
        pos.offset += ch.len_utf8();
        if ch == '\n' {
            pos.lineno += 1;
            pos.col = 0;
        } else {
            pos.col += 1;
        }
    }
    pos
}

fn append_trivia_tokens(tokens: &mut Vec<SemanticToken>, srcmap: &SourceMap) {
    for (_, entries) in srcmap.trivia() {
        for trivia in entries {
            match trivia.kind {
                TriviaKind::Keyword => {
                    tokens.push(SemanticToken::new(trivia.span, SemanticTokenKind::Keyword));
                }
                TriviaKind::Comment => {
                    tokens.push(SemanticToken::new(trivia.span, SemanticTokenKind::Comment));
                }
                TriviaKind::Operator => {
                    tokens.push(SemanticToken::new(trivia.span, SemanticTokenKind::Operator));
                }
            }
        }
    }
}

fn sort_tokens(tokens: &mut Vec<SemanticToken>) {
    tokens.sort_by(|a, b| {
        (a.span.start.lineno, a.span.start.col, a.span.start.offset).cmp(&(
            b.span.start.lineno,
            b.span.start.col,
            b.span.start.offset,
        ))
    });
}
