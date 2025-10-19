#[macro_use]
mod macros;

mod atoms;
mod collections;
mod control;
mod decl;
mod expr;
mod func;
mod imports;
mod ops;
mod recover;
mod ty;

pub use recover::Recover;

use std::{fs, io, mem};

use crate::{
    ast::{
        Block, Decl, Decorator, Expr, File, Import, Missing, Name, Node, Path, Pattern, ValueKind,
        token::{CommentKind, Token, TokenKind},
    },
    errors::{RayError, RayErrorKind},
    parse::lexer::{Lexer, Preceding},
    pathlib::FilePath,
    span::{Pos, Source, SourceMap, Span, parsed::Parsed},
    typing::ty::{Ty, TyScheme},
};

fn read_string<R: io::Read>(mut r: R) -> ParseResult<String> {
    let mut src = String::new();
    r.read_to_string(&mut src)?;
    Ok(src)
}

pub type ParseResult<T> = Result<T, RayError>;
pub type ParsedExpr = Node<Expr>;
pub type ParsedDecl = Node<Decl>;
pub type ExprResult = ParseResult<ParsedExpr>;
pub type DeclResult = ParseResult<ParsedDecl>;

bitflags::bitflags! {
    /// Contextual switches that travel with a [`ParseContext`].
    ///
    /// The parser clones the context before descending into sub‑parsers and
    /// toggles these bits to steer how the child production should behave. The
    /// flags primarily influence two things:
    ///
    /// * which constructs are permitted (e.g. disallowing `{ ... }` from being
    ///   treated as an expression in positions where only atomic expressions are
    ///   valid), and
    /// * the shape of diagnostics when recovery has to fabricate placeholders
    ///   (e.g. requiring that an expression follow a comma so the error reads
    ///   "expected expression after the previous comma").
    pub struct Restrictions: u8 {
        /// The next token must begin an expression (set after a comma);
        /// combined with `AFTER_COMMA` it gives better error messages.
        const EXPECT_EXPR   = 1 << 0;
        /// Parsing the condition/branches of an `if`/`else` chain;
        /// used to keep operators like `else` from being consumed as
        /// infix tokens in nested contexts.
        const IF_ELSE       = 1 << 1;
        /// Inside a loop; reserved for future validation such as `break`.
        const IN_LOOP       = 1 << 2;
        /// Inside a function; reserved for future validation such as `return`.
        const IN_FUNC       = 1 << 3;
        /// Expression is parsed in an r-value position (e.g. assignment rhs).
        const RVALUE        = 1 << 4;
        /// Disallow `{ ... }` from being interpreted as an expression.
        /// (needed for contexts where a block would change
        /// parsing behaviour, such as `if` conditions).
        const NO_CURLY_EXPR = 1 << 5;
        /// Set alongside `EXPECT_EXPR` to improve comma-related diagnostics.
        const AFTER_COMMA   = 1 << 6;
        /// Currently parsing inside parentheses (newline handling differs);
        /// it relaxes newline handling so multiline expressions can be parsed.
        const IN_PAREN      = 1 << 7;
    }
}

#[derive(Clone, Debug)]
pub struct ParseContext {
    pub top_level: bool,
    pub path: Path,
    pub in_func: bool,
    pub in_loop: bool,
    pub restrictions: Restrictions,
    pub stop_token: Option<TokenKind>,
}

impl ParseContext {
    pub fn new(path: Path) -> ParseContext {
        ParseContext {
            path,
            top_level: false,
            in_func: false,
            in_loop: false,
            restrictions: Restrictions::empty(),
            stop_token: None,
        }
    }

    pub fn get_vkind(&self) -> ValueKind {
        if self.restrictions.contains(Restrictions::RVALUE) {
            ValueKind::RValue
        } else {
            ValueKind::LValue
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct ParseOptions {
    pub module_path: Path,
    pub use_stdin: bool,
    pub filepath: FilePath,
    pub original_filepath: FilePath,
}

/// Result of attempting to parse a Ray source module, including any diagnostics.
#[derive(Debug)]
pub struct ParseDiagnostics<T> {
    pub value: Option<T>,
    pub errors: Vec<RayError>,
}

#[derive(Default)]
struct DocComments {
    module: Option<String>,
    item: Option<String>,
}

impl<T> ParseDiagnostics<T> {
    fn success(value: T, errors: Vec<RayError>) -> Self {
        Self {
            value: Some(value),
            errors,
        }
    }

    fn failure(err: RayError) -> Self {
        Self {
            value: None,
            errors: vec![err],
        }
    }
}

#[derive(Debug)]
pub struct StatementParseOptions {
    is_top_level: bool,
    only_functions: bool,
    allow_externs: bool,
}

struct Items {
    imports: Vec<Import>,
    decls: Vec<Node<Decl>>,
    stmts: Vec<Node<Expr>>,
}

impl Items {
    fn new() -> Items {
        Items {
            imports: vec![],
            decls: vec![],
            stmts: vec![],
        }
    }
}

pub struct Parser<'src> {
    lex: Lexer,
    options: ParseOptions,
    srcmap: &'src mut SourceMap,
    errors: Vec<RayError>,
}

impl<'src> Parser<'src> {
    pub fn parse(options: ParseOptions, srcmap: &'src mut SourceMap) -> ParseResult<File> {
        let src = Self::get_src(&options)?;
        Self::parse_from_src(&src, options, srcmap)
    }

    pub fn parse_with_diagnostics(
        options: ParseOptions,
        srcmap: &'src mut SourceMap,
    ) -> ParseDiagnostics<File> {
        let src = match Self::get_src(&options) {
            Ok(src) => src,
            Err(err) => return ParseDiagnostics::failure(err),
        };
        Self::parse_from_src_with_diagnostics(&src, options, srcmap)
    }

    pub fn parse_from_src(
        src: &str,
        options: ParseOptions,
        srcmap: &'src mut SourceMap,
    ) -> ParseResult<File> {
        let lex = Lexer::new(src);
        let mut parser = Self {
            lex,
            options,
            srcmap,
            errors: Vec::new(),
        };
        let file = parser.parse_into_file()?;
        let extra_errors = mem::take(&mut parser.errors);
        if let Some(err) = extra_errors.into_iter().next() {
            Err(err)
        } else {
            Ok(file)
        }
    }

    pub fn parse_from_src_with_diagnostics(
        src: &str,
        options: ParseOptions,
        srcmap: &'src mut SourceMap,
    ) -> ParseDiagnostics<File> {
        let lex = Lexer::new(src);
        let mut parser = Self {
            lex,
            options,
            srcmap,
            errors: Vec::new(),
        };

        match parser.parse_into_file() {
            Ok(file) => {
                let errors = mem::take(&mut parser.errors);
                ParseDiagnostics::success(file, errors)
            }
            Err(err) => {
                let mut errors = mem::take(&mut parser.errors);
                errors.insert(0, err);
                ParseDiagnostics {
                    value: None,
                    errors,
                }
            }
        }
    }

    fn get_src(options: &ParseOptions) -> ParseResult<String> {
        if options.use_stdin && options.filepath == options.original_filepath {
            // the original_filepath is the one coming from stdin
            let stdin = io::stdin();
            read_string(stdin)
        } else {
            read_string(fs::File::open(&options.filepath)?)
        }
        .map_err(|mut err| {
            err.src
                .iter_mut()
                .for_each(|src| src.filepath = options.filepath.clone());
            err
        })
    }

    fn parse_into_file(&mut self) -> ParseResult<File> {
        let path = self.options.module_path.clone();
        let ctx = ParseContext::new(path.clone());
        let DocComments {
            module: doc_comment,
            item: mut pending_doc,
        } = self.parse_doc_comments();
        let mut items = Items::new();
        let filepath = self.options.filepath.clone();
        let span = self.parse_items(Pos::new(), None, &ctx, |this, kind, doc, decs| {
            let doc = doc.or_else(|| pending_doc.take());
            match kind {
                TokenKind::Import => {
                    let import = this.parse_import(&ctx)?;
                    let end = import.span.end;
                    items.imports.push(import);
                    Ok(end)
                }
                TokenKind::Extern
                | TokenKind::Struct
                | TokenKind::Trait
                | TokenKind::TypeAlias
                | TokenKind::Impl
                | TokenKind::Modifier(_)
                | TokenKind::Fn => {
                    let decl = this.parse_decl(&kind, &ctx)?;
                    if let Some(decs) = decs {
                        this.srcmap.set_decorators(&decl, decs);
                    }
                    if let Some(doc) = doc.clone() {
                        this.srcmap.set_doc(&decl, doc);
                    }

                    let end = this.srcmap.span_of(&decl).end;
                    items.decls.push(decl);
                    Ok(end)
                }
                _ => this.parse_stmt(decs, doc, &ctx).and_then(|stmt| {
                    items.stmts.push(stmt);

                    // make sure we're at the end of the line or there's a semi-colon
                    this.expect_semi_or_eol()
                }),
            }
        })?;
        Ok(File {
            path,
            stmts: items.stmts,
            decls: items.decls,
            imports: items.imports,
            doc_comment,
            filepath,
            span,
        })
    }

    fn parse_items<
        F: FnMut(
            &mut Self,
            TokenKind,
            Option<String>,
            Option<Vec<Decorator>>,
        ) -> Result<Pos, RayError>,
    >(
        &mut self,
        start: Pos,
        stop_token: Option<TokenKind>,
        ctx: &ParseContext,
        mut f: F,
    ) -> ParseResult<Span> {
        let mut end = start;
        let stop = stop_token.as_ref();

        while !self.is_eof() {
            let DocComments {
                module: _,
                item: doc,
            } = self.parse_doc_comments();
            let decs = match self.parse_decorators(end, ctx) {
                Ok((dec, span)) => {
                    end = span.end;
                    Some(dec)
                }
                Err(e) => return Err(e),
            };

            let kind = match (self.peek_kind(), stop_token.as_ref()) {
                (k, Some(stop)) if &k == stop => break,
                (TokenKind::EOF, _) => break,
                (k, _) => k,
            };

            let mut should_break = false;
            let next_end =
                f(self, kind, doc, decs).recover_with(self, stop, |parser, recovered| {
                    if let Some(stop_token) = stop {
                        if parser.peek_kind().similar_to(stop_token) {
                            should_break = true;
                        }
                    }
                    if parser.is_eof() {
                        should_break = true;
                    }
                    recovered
                });
            if next_end > end {
                end = next_end;
            }
            if should_break {
                break;
            }
        }

        Ok(Span { start, end })
    }

    fn record_parse_error(&mut self, err: RayError) {
        self.errors.push(err);
    }

    fn recover_after_error(&mut self, stop_token: Option<&TokenKind>) -> Pos {
        let mut depth: usize = 0;
        let mut last_end = self.lex.position();
        let mut consumed_any = false;

        while !self.is_eof() {
            let kind = self.peek_kind();
            if depth == 0 {
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        break;
                    }
                }
                if matches!(kind, TokenKind::EOF) {
                    break;
                }
                if matches!(kind, TokenKind::RightCurly) {
                    break;
                }
                if matches!(kind, TokenKind::RightParen | TokenKind::Comma) {
                    break;
                }
                if Self::is_decl_start(&kind) {
                    break;
                }
                if matches!(kind, TokenKind::NewLine) {
                    let tok = self.lex.token();
                    last_end = tok.span.end;
                    consumed_any = true;
                    break;
                }
            }

            let tok = self.lex.token();
            last_end = tok.span.end;
            consumed_any = true;
            match tok.kind {
                TokenKind::LeftCurly => depth += 1,
                TokenKind::RightCurly => {
                    if depth == 0 {
                        break;
                    } else {
                        depth = depth.saturating_sub(1);
                    }
                }
                _ => {}
            }
        }

        if consumed_any {
            last_end
        } else {
            self.lex.position()
        }
    }

    fn is_decl_start(kind: &TokenKind) -> bool {
        matches!(
            kind,
            TokenKind::Fn
                | TokenKind::UpperFn
                | TokenKind::Struct
                | TokenKind::Trait
                | TokenKind::Enum
                | TokenKind::TypeAlias
                | TokenKind::Impl
                | TokenKind::Extern
                | TokenKind::Object
                | TokenKind::Import
                | TokenKind::Modifier(_)
        )
    }

    fn recover_after_sequence_error(&mut self, stop_token: Option<&TokenKind>) {
        let mut depth: usize = 0;
        while !self.is_eof() {
            let kind = self.peek_kind();
            if depth == 0 {
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        break;
                    }
                }
                if matches!(
                    kind,
                    TokenKind::Comma | TokenKind::RightCurly | TokenKind::NewLine
                ) {
                    break;
                }
            }

            let tok = self.lex.token();
            match tok.kind {
                TokenKind::LeftParen | TokenKind::LeftBracket | TokenKind::LeftCurly => depth += 1,
                TokenKind::RightParen | TokenKind::RightBracket | TokenKind::RightCurly => {
                    if depth == 0 {
                        break;
                    } else {
                        depth = depth.saturating_sub(1);
                    }
                }
                _ => {}
            }
        }
    }

    fn missing_expr(&mut self, start: Pos, mut end: Pos, ctx: &ParseContext) -> ParsedExpr {
        if end.offset < start.offset {
            end = start;
        }
        let span = Span { start, end };
        let context = Some(ctx.path.to_string());
        let missing = Missing::new("expression", context);
        self.mk_expr(Expr::Missing(missing), span, ctx.path.clone())
    }

    fn missing_block_expr(&mut self, start: Pos, mut end: Pos, ctx: &ParseContext) -> ParsedExpr {
        if end.offset < start.offset {
            end = start;
        }
        let span = Span { start, end };
        let context = Some(ctx.path.to_string());
        let missing = Missing::new("block", context);
        self.mk_expr(Expr::Missing(missing), span, ctx.path.clone())
    }

    fn missing_pattern(&mut self, start: Pos, mut end: Pos, ctx: &ParseContext) -> Node<Pattern> {
        if end.offset < start.offset {
            end = start;
        }
        let span = Span { start, end };
        let context = Some(ctx.path.to_string());
        let missing = Missing::new("pattern", context);
        self.mk_node(Pattern::Missing(missing), span)
    }

    fn missing_type(&mut self, start: Pos, mut end: Pos) -> Parsed<TyScheme> {
        if end.offset < start.offset {
            end = start;
        }
        let span = Span { start, end };
        Parsed::new(TyScheme::from_mono(Ty::Never), self.mk_src(span))
    }

    fn parse_type_annotation(&mut self, stop: Option<&TokenKind>) -> Parsed<TyScheme> {
        let start = self.lex.position();
        let next_kind = self.peek_kind();
        let mut should_short_circuit = stop
            .map(|stop_kind| next_kind.similar_to(stop_kind))
            .unwrap_or(false);
        if !should_short_circuit {
            should_short_circuit = matches!(
                next_kind,
                TokenKind::RightParen
                    | TokenKind::RightCurly
                    | TokenKind::Comma
                    | TokenKind::Semi
                    | TokenKind::NewLine
                    | TokenKind::EOF
            );
        }

        if should_short_circuit {
            if matches!(next_kind, TokenKind::EOF) {
                let err = self.unexpected_eof(start);
                self.record_parse_error(err);
                return self.missing_type(start, self.lex.position());
            } else {
                let peek_token = self.lex.peek_token().clone();
                let err = self.unexpected_token(&peek_token, "type");
                self.record_parse_error(err);
                return self.missing_type(start, peek_token.span.start);
            }
        }

        self.parse_ty()
            .recover_with(self, stop, |parser, recovered| {
                parser.missing_type(start, recovered)
            })
    }

    fn parse_doc_comments(&mut self) -> DocComments {
        if self.lex.peek_preceding().is_empty() {
            return DocComments::default();
        }

        let preceding = self.lex.preceding();
        if preceding.is_empty() {
            return DocComments::default();
        }

        let mut module_lines: Vec<String> = vec![];
        let mut item_lines: Vec<String> = vec![];

        for p in preceding {
            if let Preceding::Comment(c) = p {
                if let TokenKind::Comment { ref content, kind } = c.kind {
                    let line = if let Some(stripped) = content.strip_prefix(' ') {
                        stripped.to_owned()
                    } else {
                        content.clone()
                    };

                    match kind {
                        CommentKind::ModuleDoc => module_lines.push(line),
                        CommentKind::Doc => item_lines.push(line),
                        CommentKind::Line => {}
                    }
                }
            }
        }

        if !module_lines.is_empty() {
            log::debug!("[parser] module doc comment: {:?}", module_lines);
        }
        if !item_lines.is_empty() {
            log::debug!("[parser] doc comment: {:?}", item_lines);
        }

        DocComments {
            module: if module_lines.is_empty() {
                None
            } else {
                Some(module_lines.join("\n"))
            },
            item: if item_lines.is_empty() {
                None
            } else {
                Some(item_lines.join("\n"))
            },
        }
    }

    fn parse_stmt(
        &mut self,
        decs: Option<Vec<Decorator>>,
        doc: Option<String>,
        ctx: &ParseContext,
    ) -> ExprResult {
        let expr = self.parse_expr(ctx)?;
        if let Some(decs) = decs {
            self.srcmap.set_decorators(&expr, decs)
        }
        if let Some(doc) = doc {
            self.srcmap.set_doc(&expr, doc);
        }
        Ok(expr)
    }

    fn is_eof(&mut self) -> bool {
        self.lex.peek_token().kind == TokenKind::EOF
    }

    fn token(&mut self) -> ParseResult<Token> {
        let start = self.lex.position();
        let tok = self.lex.token();
        match tok.kind {
            TokenKind::EOF => Err(self.unexpected_eof(start)),
            _ => Ok(tok),
        }
    }

    fn peek_kind(&mut self) -> TokenKind {
        self.lex.peek_token().kind.clone()
    }

    fn peek_kind_at(&mut self, idx: usize) -> TokenKind {
        self.lex.peek_token_at(idx).kind.clone()
    }

    fn must_peek_kind(&mut self) -> ParseResult<TokenKind> {
        let start = self.lex.position();
        match self.peek_kind() {
            TokenKind::EOF => Err(self.unexpected_eof(start)),
            k => Ok(k),
        }
    }

    fn is_next_expr_begin(&mut self) -> bool {
        match self.peek_kind() {
            TokenKind::Identifier(s)
                if &s == "b"
                    && matches!(
                        self.peek_kind_at(1),
                        TokenKind::SingleQuote | TokenKind::DoubleQuote
                    ) =>
            {
                true
            }
            TokenKind::Integer { .. }
            | TokenKind::Float { .. }
            | TokenKind::SingleQuote { .. }
            | TokenKind::DoubleQuote { .. }
            | TokenKind::Bool(..)
            | TokenKind::Nil
            | TokenKind::If
            | TokenKind::For
            | TokenKind::While
            | TokenKind::Loop
            | TokenKind::Fn
            | TokenKind::LeftParen
            | TokenKind::LeftCurly
            | TokenKind::Mut
            | TokenKind::Identifier(_)
            | TokenKind::LeftBracket => true,
            _ => false,
        }
    }

    pub(crate) fn mk_expr(&mut self, expr: Expr, span: Span, path: Path) -> ParsedExpr {
        let node = Node::new(expr);
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            path,
            src_module: self.options.module_path.clone(),
        };
        self.srcmap.set_src(&node, src);

        node
    }

    pub(crate) fn mk_ty(&mut self, ty: Parsed<Ty>, path: Path) -> Node<Parsed<Ty>> {
        let span = *ty.span().unwrap();
        let node = Node::new(ty);
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            path,
            src_module: self.options.module_path.clone(),
        };
        self.srcmap.set_src(&node, src);
        node
    }

    pub(crate) fn mk_tyscheme(
        &mut self,
        ty: Parsed<TyScheme>,
        path: Path,
    ) -> Node<Parsed<TyScheme>> {
        let span = *ty.span().unwrap();
        let node = Node::new(ty);
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            path,
            src_module: self.options.module_path.clone(),
        };
        self.srcmap.set_src(&node, src);
        node
    }

    pub(crate) fn mk_decl(&mut self, decl: Decl, span: Span, path: Path) -> ParsedDecl {
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            path,
            src_module: self.options.module_path.clone(),
        };
        let node = Node::new(decl);
        self.srcmap.set_src(&node, src);
        node
    }

    pub(crate) fn mk_node<T>(&mut self, value: T, span: Span) -> Node<T> {
        let node = Node::new(value);
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            ..Default::default()
        };
        self.srcmap.set_src(&node, src);
        node
    }

    pub(crate) fn mk_node_with_path<T>(&mut self, value: T, span: Span, path: Path) -> Node<T> {
        let node = Node::new(value);
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            path,
            src_module: self.options.module_path.clone(),
        };
        self.srcmap.set_src(&node, src);
        node
    }

    pub(crate) fn mk_src(&self, span: Span) -> Source {
        Source {
            filepath: self.options.filepath.clone(),
            span: Some(span),
            src_module: self.options.module_path.clone(),
            ..Default::default()
        }
    }

    fn expect(&mut self, kind: TokenKind) -> ParseResult<(Token, Span)> {
        let tok = self.token()?;
        let span = tok.span;

        if tok.kind.similar_to(&kind) {
            Ok((tok, span))
        } else {
            Err(self.unexpected_token(&tok, kind.desc()))
        }
    }

    fn expect_kind(&mut self, kind: TokenKind) -> ParseResult<Option<Token>> {
        let is_kind = self.lex.peek_token().kind == kind;
        Ok(if is_kind {
            let tok = self.token()?;
            Some(tok)
        } else {
            None
        })
    }

    fn expect_string(&mut self) -> ParseResult<(String, Span)> {
        let start = self.expect_start(TokenKind::DoubleQuote)?;
        let (s, terminated) = self.lex.quoted_string('"');
        let end = self.lex.position();
        if !terminated {
            return Err(self.unexpected_eof(end));
        }

        Ok((s, Span { start, end }))
    }

    fn expect_char(&mut self) -> ParseResult<(String, Span)> {
        let start = self.expect_start(TokenKind::SingleQuote)?;
        let (s, terminated) = self.lex.quoted_string('\'');
        let end = self.lex.position();
        if !terminated {
            return Err(self.unexpected_eof(end));
        }

        Ok((s, Span { start, end }))
    }

    fn expect_ty_var_ident(&mut self) -> ParseResult<(String, Span)> {
        let start = self.expect_start(TokenKind::SingleQuote)?;
        let (mut ident, Span { end, .. }) = self.expect_id()?;
        ident.insert(0, '\'');
        Ok((ident, Span { start, end }))
    }

    fn expect_id(&mut self) -> ParseResult<(String, Span)> {
        let tok = self.token()?;
        let span = tok.span;
        match tok.kind {
            TokenKind::Identifier(_) | TokenKind::Struct | TokenKind::Underscore => {
                Ok((tok.kind.to_string(), span))
            }
            _ => Err(self.unexpected_token(&tok, "identifier")),
        }
    }

    fn expect_sp(&mut self, kind: TokenKind) -> ParseResult<Span> {
        let tok = self.token()?;
        if tok.kind.similar_to(&kind) {
            Ok(tok.span)
        } else {
            Err(self.unexpected_token(&tok, kind.desc()))
        }
    }

    fn expect_start(&mut self, kind: TokenKind) -> ParseResult<Pos> {
        Ok(self.expect_sp(kind)?.start)
    }

    fn expect_end(&mut self, kind: TokenKind) -> ParseResult<Pos> {
        Ok(self.expect_sp(kind)?.end)
    }

    fn expect_semi_or_eol(&mut self) -> ParseResult<Pos> {
        if self.is_eol() {
            Ok(self.lex.position())
        } else {
            let tok = self.token()?;
            let span = tok.span;
            match tok.kind {
                TokenKind::NewLine | TokenKind::Semi => Ok(span.start),
                _ => Err(self.unexpected_token(&tok, "`;` or a new line")),
            }
        }
    }

    fn expect_matching(&mut self, start: &Token, end: TokenKind) -> ParseResult<Pos> {
        let kind = self.peek_kind();
        if !kind.similar_to(&end) {
            let end_pos = self.lex.position();
            return Err(self.parse_error(
                format!(
                    "expected a matching `{}` at {} for `{}`, but found `{}`",
                    end, end_pos, start.kind, kind
                ),
                Span {
                    start: start.span.start,
                    end: end_pos,
                },
            ));
        }

        self.expect_end(end)
    }

    /// Determine if the lexer is currently at the end of a line
    /// First, we peek the next token with the preceding whitespace
    /// and comments if there is a newline token in the preceding,
    /// then the lexer must be at the end of the current line
    fn is_eol(&mut self) -> bool {
        self.is_eof()
            || self.lex.peek_preceding().iter().any(|p| match p {
                Preceding::Whitespace(t) | Preceding::Comment(t) => {
                    t.kind == TokenKind::NewLine || t.span.lines() > 1
                }
            })
    }

    fn parse_error(&self, msg: String, span: Span) -> RayError {
        RayError {
            msg,
            src: vec![Source {
                span: Some(span),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Parse,
        }
    }

    fn unexpected_eof(&mut self, start: Pos) -> RayError {
        let end = self.lex.position();
        RayError {
            msg: format!("unexpected end of file"),
            src: vec![Source {
                span: Some(Span { start, end }),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Parse,
        }
    }

    fn unexpected_token(&self, tok: &Token, expected: &str) -> RayError {
        RayError {
            msg: format!("expected {}, but found `{}`", expected, tok),
            src: vec![Source {
                span: Some(tok.span),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Parse,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ParseDiagnostics, ParseOptions, Parser};
    use crate::{
        ast::{Decl, Expr, Func, InfixOp, Literal, Path, Pattern},
        errors::{RayError, RayErrorKind},
        pathlib::FilePath,
        span::SourceMap,
        typing::ty::Ty,
    };

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
        let options = test_options();
        let ParseDiagnostics { value, errors } =
            Parser::parse_from_src_with_diagnostics(src, options, &mut srcmap);
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
            other => panic!("expected block expression, got {:?}", other),
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
        assert_eq!(result.errors[0].kind, RayErrorKind::Parse);
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
        assert!(
            !errors.is_empty(),
            "expected errors for tuple type element"
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
        assert!(
            if_expr.els.is_none(),
            "expected parser to drop else branch after recovery, got {:?}",
            if_expr.els.as_ref().map(|els| &els.value)
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
                    missing.expected, "block",
                    "expected placeholder block expression"
                );
            }
            other => panic!("expected missing block expression, got {:?}", other),
        }
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
                    missing.expected, "block",
                    "expected placeholder empty for body"
                );
            }
            other => panic!("expected missing block expression, got {:?}", other),
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
                    missing.expected, "block",
                    "expected placeholder empty while body"
                );
            }
            other => panic!("expected missing block expression, got {:?}", other),
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
                    missing.expected, "block",
                    "expected placeholder empty loop body"
                );
            }
            other => panic!("expected missing block expression, got {:?}", other),
        }
    }
}
