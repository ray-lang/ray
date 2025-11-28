#[macro_use]
mod macros;

mod atoms;
mod collections;
mod context;
mod control;
mod decl;
mod expr;
mod func;
mod imports;
mod ops;
mod recover;
mod ty;

#[cfg(test)]
mod tests;

pub use context::ParseContext;
use ray_shared::node_id::NodeId;
pub use recover::{Recover, RecoveryCtx};

use std::{fs, io, mem};

use rand::RngCore;
use ray_shared::pathlib::{FilePath, Path};
use ray_shared::span::{Pos, Source, Span, parsed::Parsed};
use ray_typing::types::{Ty, TyScheme};

use crate::{
    ast::{
        Decl, Decorator, Expr, File, Import, InfixOp, Missing, Node, Pattern, TrailingPolicy,
        token::{CommentKind, Token, TokenKind},
    },
    errors::{RayError, RayErrorKind},
    parse::{
        lexer::{Lexer, NewlineMode, Preceding},
        parser::context::{ParseScope, SeqSpec},
    },
    sourcemap::{SourceMap, TriviaKind},
};

const DEPTH_IDX_PAREN: usize = 0;
const DEPTH_IDX_BRACKET: usize = 1;
const DEPTH_IDX_CURLY: usize = 2;

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
    pub struct Restrictions: u16 {
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
        /// The parsing is at the top-level
        const AT_TOP_LEVEL  = 1 << 8;
    }
}

#[derive(Clone, Debug, Default)]
pub struct ParseOptions {
    pub module_path: Path,
    pub use_stdin: bool,
    pub filepath: FilePath,
    pub original_filepath: FilePath,
}

#[derive(Default)]
struct DocComments {
    module: Option<String>,
    item: Option<String>,
}

/// Result of attempting to parse a Ray source module, including any diagnostics.
#[derive(Debug)]
pub struct ParseDiagnostics<T> {
    pub value: Option<T>,
    pub errors: Vec<RayError>,
}

impl<T> Into<Result<T, Vec<RayError>>> for ParseDiagnostics<T> {
    fn into(self) -> Result<T, Vec<RayError>> {
        if !self.errors.is_empty() {
            return Err(self.errors);
        }

        if let Some(value) = self.value {
            return Ok(value);
        }

        // we shouldn't get here, because we should either have:
        // - a value with zero or more errors
        // - no value and zero or more errors
        Err(vec![RayError {
            msg: "unknown error".to_string(),
            src: vec![],
            kind: RayErrorKind::Unknown,
            context: None,
        }])
    }
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

#[allow(dead_code)]
struct Expect<'a> {
    parser: &'a mut Parser<'a>,
    kind: Option<TokenKind>,
    result: Option<ParseResult<Token>>,
}

#[allow(dead_code)]
impl<'a> Expect<'a> {
    fn kind(parser: &'a mut Parser<'a>, kind: TokenKind) -> Expect<'a> {
        Expect {
            parser,
            kind: Some(kind),
            result: None,
        }
    }

    fn error(parser: &'a mut Parser<'a>, err: RayError) -> Expect<'a> {
        Expect {
            parser,
            kind: None,
            result: Some(Err(err)),
        }
    }

    fn consume(self) -> Expect<'a> {
        let parser = self.parser;
        if let Some(kind) = self.kind {
            let tok = parser.peek();
            if tok.kind.similar_to(&kind) {
                let _ = match parser.token() {
                    Ok(tok) => tok,
                    Err(err) => return Expect::error(parser, err),
                };
            }
        }

        Expect {
            parser,
            kind: None,
            result: None,
        }
    }

    fn record(self) -> Expect<'a> {
        let tok = match &self.result {
            Some(Ok(tok)) => tok,
            _ => return self,
        };

        let kind = match tok.kind {
            TokenKind::Ampersand | TokenKind::Arrow | TokenKind::Asterisk => TriviaKind::Operator,
            _ => return self,
        };
        self.parser
            .record_trivia(kind, tok.span, Some(tok.kind.clone()));
        self
    }
}

pub struct Parser<'src> {
    lex: Lexer,
    options: ParseOptions,
    srcmap: &'src mut SourceMap,
    errors: Vec<RayError>,
}

impl<'src> Parser<'src> {
    pub fn new(src: &str, options: ParseOptions, srcmap: &'src mut SourceMap) -> Self {
        let lex = Lexer::new(src);
        Self {
            lex,
            options,
            srcmap,
            errors: Vec::new(),
        }
    }

    pub fn parse(options: ParseOptions, srcmap: &'src mut SourceMap) -> ParseDiagnostics<File> {
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

    pub fn parse_from_src_with_diagnostics(
        src: &str,
        options: ParseOptions,
        srcmap: &'src mut SourceMap,
    ) -> ParseDiagnostics<File> {
        let mut parser = Parser::new(src, options, srcmap);
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

    fn with_scope<'a>(&'a mut self, ctx: &ParseContext) -> ParseScope<'a, 'src> {
        ParseScope {
            p: self,
            undo: vec![],
            ctx: ctx.clone(),
        }
    }

    fn with_path_scope<'a>(&'a mut self, path: &Path) -> ParseScope<'a, 'src> {
        ParseScope {
            p: self,
            undo: vec![],
            ctx: ParseContext::new(path.clone()),
        }
    }

    fn parse_into_file(&mut self) -> ParseResult<File> {
        let path = self.options.module_path.clone();
        let mut parser = self.with_path_scope(&path);
        let DocComments {
            module: doc_comment,
            item: mut pending_doc,
        } = parser.parse_doc_comments();
        let mut items = Items::new();
        let filepath = parser.options.filepath.clone();
        parser = parser.with_newline_mode(NewlineMode::Emit);
        let ctx = parser.ctx_clone();
        let span = parser.parse_items(Pos::empty(), None, &ctx, |this, kind, doc, decs| {
            log::debug!("[parse_item] decs={:?}", decs);
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
                    if let Some(decs) = decs
                        && decs.len() > 0
                    {
                        this.srcmap.set_decorators(&decl, decs);
                    }
                    if let Some(doc) = doc.clone() {
                        this.srcmap.set_doc(&decl, doc);
                    }

                    let end = this.srcmap.span_of(&decl).end;
                    items.decls.push(decl);
                    Ok(end)
                }
                _ => {
                    this.parse_stmt(decs, doc, &ctx)
                        .map_err(|err| {
                            if err.kind == RayErrorKind::UnexpectedToken {
                                let tok = this.peek();
                                let msg = format!(
                                    "expected a top-level statement or expression, but found `{}`",
                                    tok
                                );
                                return RayError {
                                    msg,
                                    src: err.src,
                                    kind: RayErrorKind::Parse,
                                    context: err.context,
                                };
                            }

                            err
                        })
                        .and_then(|stmt| {
                            items.stmts.push(stmt);

                            // make sure we're at the end of the line or there's a semi-colon
                            this.expect_semi_or_eol(&ctx)
                        })
                }
            }
        })?;

        // Drain any trivia (comments) that remain before EOF so they are recorded.
        for trivia in parser.lex.preceding() {
            if let Preceding::Comment(comment_tok) = trivia {
                parser.record_trivia(TriviaKind::Comment, comment_tok.span, None);
            }
        }

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

        'items: while !self.is_eof() {
            while matches!(self.peek_kind(), TokenKind::NewLine) {
                self.expect(TokenKind::NewLine, ctx)?;
                continue 'items;
            }

            let DocComments {
                module: _,
                item: doc,
            } = self.parse_doc_comments();
            let decs = match self.parse_decorators(end, ctx) {
                Ok((dec, _)) => {
                    if dec.is_some() && matches!(self.peek_kind(), TokenKind::NewLine) {
                        end = self.expect_end(TokenKind::NewLine, ctx)?;
                    }
                    dec
                }
                Err(e) => return Err(e),
            };

            let kind = match (self.peek_kind(), stop_token.as_ref()) {
                (k, Some(stop)) if &k == stop => break,
                (TokenKind::EOF, _) => break,
                (k, _) => k,
            };

            let mut should_break = false;
            let next_end = f(self, kind, doc, decs).recover_with_ctx(
                self,
                RecoveryCtx::stmt(stop)
                    .with_newline(true)
                    .with_decl_stops(false),
                |parser, recovered| {
                    if let Some(stop_token) = stop {
                        if parser.peek_kind().similar_to(stop_token) {
                            should_break = true;
                        }
                    }
                    if parser.is_eof() {
                        should_break = true;
                    }
                    recovered
                },
            );
            if next_end > end {
                end = next_end;
            }
            if should_break {
                break;
            }
        }

        Ok(Span { start, end })
    }

    fn parse_delimited_seq<T, F>(
        &mut self,
        spec: SeqSpec,
        ctx: &ParseContext,
        mut f: F,
    ) -> ParseResult<(T, Option<(Span, Span)>)>
    where
        F: FnMut(&mut Self, TrailingPolicy, Option<TokenKind>, &ParseContext) -> ParseResult<T>,
    {
        let mut parser = self
            .with_scope(ctx)
            .with_newline_mode(spec.newline)
            .with_restrictions(spec.restrictions);
        let ctx = parser.ctx_clone();

        let (start_tok, end_kind) = if let Some((start_delim, end_delim)) = &spec.delimiters {
            if matches!(start_delim, TokenKind::LeftCurly) {
                parser.consume_newlines(&ctx)?;
            }

            if !parser.peek_kind().similar_to(start_delim) {
                let tok = parser.peek();
                return Err(parser.unexpected_token(&tok, start_delim.desc(), &ctx));
            }

            let start_tok = parser.token()?;
            (Some(start_tok), Some(end_delim.clone()))
        } else {
            (None, None)
        };

        let stop_token = end_kind.clone();
        let seq = f(&mut parser, spec.trailing, stop_token, &ctx)?;

        Ok(if let Some(end_delim) = end_kind {
            let start_tok = start_tok.expect("delimiter start token missing");
            let next_kind = parser.peek_kind();
            if !next_kind.similar_to(&end_delim) {
                let end_pos = parser.lex.position();
                return Err(parser.parse_error(
                    format!(
                        "expected a matching `{}` at {} for `{}`, but found `{}`",
                        end_delim, end_pos, start_tok.kind, next_kind
                    ),
                    Span {
                        start: start_tok.span.start,
                        end: end_pos,
                    },
                    &ctx,
                ));
            }
            let end_tok = parser.expect(end_delim, &ctx)?;
            log::debug!(
                "[parse_delimited_seq] matched start token {:?} to end token {:?}",
                start_tok,
                end_tok
            );
            (seq, Some((start_tok.span, end_tok.span)))
        } else {
            (seq, None)
        })
    }

    fn parse_sep_seq<T, F>(
        &mut self,
        separator: &TokenKind,
        trailing: TrailingPolicy,
        stop: Option<&TokenKind>,
        ctx: &ParseContext,
        mut parse_elem: F,
    ) -> ParseResult<(Vec<T>, bool)>
    where
        F: FnMut(&mut Self, &ParseContext) -> ParseResult<T>,
    {
        let mut items = Vec::new();
        let mut trailing_sep = false;
        let mut last_sep_span = None;
        let seq_ctx = RecoveryCtx::default_seq(stop)
            .with_trailing(trailing)
            .with_newline(false);

        loop {
            if let Some(stop_tok) = stop {
                if self.peek_kind().similar_to(stop_tok) {
                    break;
                }
            }
            if self.is_eof() {
                break;
            }

            let parsed =
                parse_elem(self, ctx)
                    .map(Some)
                    .recover_seq_with_ctx(self, seq_ctx.clone(), |_| None);

            let Some(item) = parsed else {
                // recovery consumed tokens; re-evaluate stop/separator.
                if let Some(stop_tok) = stop {
                    if self.peek_kind().similar_to(stop_tok) {
                        break;
                    }
                }
                if self.is_eof() {
                    break;
                }
                continue;
            };

            items.push(item);
            trailing_sep = false;

            if !self.peek_kind().similar_to(separator) {
                break;
            }

            let sep_tok = self.expect(separator.clone(), ctx)?;
            last_sep_span = Some(sep_tok.span);
            trailing_sep = true;
        }

        if trailing_sep && matches!(trailing, TrailingPolicy::Forbid) {
            if let Some(span) = last_sep_span {
                let err = self.parse_error(
                    format!("unexpected trailing `{}`", separator.desc()),
                    span,
                    ctx,
                );
                self.record_parse_error(err);
            }
        }

        Ok((items, trailing_sep))
    }

    fn record_parse_error(&mut self, err: RayError) {
        if let Some(last_err) = self.errors.last() {
            if last_err == &err {
                // This is guardrail to prevent looping on the same location
                let tok = self.lex.token();
                log::debug!(
                    "[record parse error] DUPLICATE ERROR: consuming token {:?}",
                    tok
                );
                return;
            }
        }

        log::debug!("[record parse error] {:#?}", err);
        self.errors.push(err);
    }

    fn recover_stmt_with_ctx(&mut self, ctx: RecoveryCtx<'_>) -> Pos {
        let stop = ctx.stop;
        match ctx.mode {
            recover::RecoveryMode::Stmt {
                newline_breaks,
                decl_stops,
            } => self.recover_stmt(stop, newline_breaks, decl_stops),
            recover::RecoveryMode::Expr {
                ternary_sensitive,
                last_op,
                newline_breaks,
            } => self.recover_expr(stop, ternary_sensitive, last_op, newline_breaks),
            _ => self.recover_after_error(stop),
        }
    }

    fn recover_seq_with_ctx(&mut self, ctx: RecoveryCtx<'_>) {
        match ctx.mode {
            recover::RecoveryMode::Seq {
                delimiter,
                trailing,
                newline_breaks,
            } => self.recover_seq(ctx.stop, delimiter, trailing, newline_breaks),
            _ => self.recover_after_sequence_error(ctx.stop),
        }
    }

    fn recover_expr(
        &mut self,
        stop_token: Option<&TokenKind>,
        ternary_sensitive: bool,
        last_op: Option<InfixOp>,
        newline_breaks: bool,
    ) -> Pos {
        let mut depth = [0usize; 3];
        let mut last_end = self.lex.position();
        let mut consumed_any = false;

        while !self.is_eof() {
            let kind = self.peek_kind();
            let depth_zero = depth.iter().all(|&d| d == 0);

            if depth_zero {
                if newline_breaks && matches!(kind, TokenKind::NewLine) {
                    break;
                }

                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        break;
                    }
                }

                if matches!(
                    kind,
                    TokenKind::Comma | TokenKind::Semi | TokenKind::NewLine
                ) {
                    break;
                }

                if matches!(
                    kind,
                    TokenKind::RightParen | TokenKind::RightBracket | TokenKind::RightCurly
                ) {
                    break;
                }

                if ternary_sensitive && matches!(kind, TokenKind::Else | TokenKind::Question) {
                    break;
                }

                if let Some(op) = &last_op {
                    if op.matches_token_kind(&kind) {
                        let tok = self.lex.token();
                        last_end = tok.span.end;
                        consumed_any = true;
                        break;
                    }
                }
            }

            let tok = self.lex.token();
            last_end = tok.span.end;
            consumed_any = true;
            match tok.kind {
                TokenKind::LeftParen => depth[DEPTH_IDX_PAREN] += 1,
                TokenKind::RightParen => {
                    depth[DEPTH_IDX_PAREN] = depth[DEPTH_IDX_PAREN].saturating_sub(1)
                }
                TokenKind::LeftBracket => depth[DEPTH_IDX_BRACKET] += 1,
                TokenKind::RightBracket => {
                    depth[DEPTH_IDX_BRACKET] = depth[DEPTH_IDX_BRACKET].saturating_sub(1)
                }
                TokenKind::LeftCurly => depth[DEPTH_IDX_CURLY] += 1,
                TokenKind::RightCurly => {
                    if depth[DEPTH_IDX_CURLY] == 0 {
                        break;
                    }
                    depth[DEPTH_IDX_CURLY] -= 1;
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

    fn recover_seq(
        &mut self,
        stop_token: Option<&TokenKind>,
        delimiter: recover::Delimiter,
        trailing: TrailingPolicy,
        newline_breaks: bool,
    ) {
        let mut depth = [0usize; 3];

        while !self.is_eof() {
            let kind = self.peek_kind();
            let depth_zero = depth.iter().all(|&d| d == 0);

            if depth_zero {
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        break;
                    }
                }

                match (delimiter, &kind) {
                    (recover::Delimiter::Paren, TokenKind::RightParen)
                    | (recover::Delimiter::Bracket, TokenKind::RightBracket)
                    | (recover::Delimiter::Curly, TokenKind::RightCurly) => break,
                    _ => {}
                }

                if newline_breaks && matches!(kind, TokenKind::NewLine) {
                    break;
                }

                if matches!(kind, TokenKind::Comma) {
                    let _ = self.lex.token();
                    if matches!(trailing, TrailingPolicy::Warn | TrailingPolicy::Forbid) {
                        // TODO: emit diagnostic note for auto-consuming a disallowed comma.
                    }
                    break;
                }
            }

            let tok = self.lex.token();
            match tok.kind {
                TokenKind::LeftParen => depth[DEPTH_IDX_PAREN] += 1,
                TokenKind::RightParen => {
                    if depth[DEPTH_IDX_PAREN] == 0 {
                        if matches!(delimiter, recover::Delimiter::Paren) {
                            break;
                        }
                    } else {
                        depth[DEPTH_IDX_PAREN] -= 1;
                    }
                }
                TokenKind::LeftBracket => depth[DEPTH_IDX_BRACKET] += 1,
                TokenKind::RightBracket => {
                    if depth[DEPTH_IDX_BRACKET] == 0 {
                        if matches!(delimiter, recover::Delimiter::Bracket) {
                            break;
                        }
                    } else {
                        depth[DEPTH_IDX_BRACKET] -= 1;
                    }
                }
                TokenKind::LeftCurly => depth[DEPTH_IDX_CURLY] += 1,
                TokenKind::RightCurly => {
                    if depth[DEPTH_IDX_CURLY] == 0 {
                        if matches!(delimiter, recover::Delimiter::Curly) {
                            break;
                        }
                    } else {
                        depth[DEPTH_IDX_CURLY] -= 1;
                    }
                }
                _ => {}
            }
        }
    }

    fn recover_stmt(
        &mut self,
        stop_token: Option<&TokenKind>,
        newline_breaks: bool,
        decl_stops: bool,
    ) -> Pos {
        let mut depth = [0usize; 3]; // paren, bracket, curly
        let mut last_end = self.lex.position();
        let mut consumed_any = false;
        let mut stopped_on_guard = false;
        let start_pos = self.lex.position();

        while !self.is_eof() {
            let kind = self.peek_kind();
            let depth_zero = depth.iter().all(|&d| d == 0);

            if depth_zero {
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        stopped_on_guard = true;
                        break;
                    }
                }

                if matches!(
                    kind,
                    TokenKind::RightCurly | TokenKind::RightParen | TokenKind::RightBracket
                ) {
                    stopped_on_guard = true;
                    break;
                }

                if decl_stops && Self::is_decl_start(&kind) {
                    stopped_on_guard = true;
                    break;
                }

                if matches!(kind, TokenKind::Semi) {
                    let tok = self.lex.token();
                    last_end = tok.span.end;
                    consumed_any = true;
                    break;
                }

                if newline_breaks && matches!(kind, TokenKind::NewLine) {
                    stopped_on_guard = true;
                    break;
                }
            }

            let tok = self.lex.token();
            last_end = tok.span.end;
            consumed_any = true;
            match tok.kind {
                TokenKind::LeftParen => depth[DEPTH_IDX_PAREN] += 1,
                TokenKind::RightParen => {
                    depth[DEPTH_IDX_PAREN] = depth[DEPTH_IDX_PAREN].saturating_sub(1)
                }
                TokenKind::LeftBracket => depth[DEPTH_IDX_BRACKET] += 1,
                TokenKind::RightBracket => {
                    depth[DEPTH_IDX_BRACKET] = depth[DEPTH_IDX_BRACKET].saturating_sub(1)
                }
                TokenKind::LeftCurly => depth[DEPTH_IDX_CURLY] += 1,
                TokenKind::RightCurly => {
                    if depth[DEPTH_IDX_CURLY] == 0 {
                        break;
                    }
                    depth[DEPTH_IDX_CURLY] -= 1;
                }
                _ => {}
            }
        }

        if consumed_any {
            last_end
        } else {
            if stopped_on_guard {
                self.lex.position()
            } else if !self.is_eof() && self.lex.position() == start_pos {
                let tok = self.lex.token();
                tok.span.end
            } else {
                self.lex.position()
            }
        }
    }

    fn recover_after_error(&mut self, stop_token: Option<&TokenKind>) -> Pos {
        let mut depth: usize = 0;
        let mut last_end = self.lex.position();
        let mut consumed_any = false;

        while !self.is_eof() {
            let kind = self.peek_kind();
            if depth == 0 {
                // Stop if caller-provided stop token is ahead.
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        // Ensure progress by consuming exactly one token if we haven't yet.
                        if !consumed_any && !self.is_eof() {
                            let tok = self.lex.token();
                            last_end = tok.span.end;
                            consumed_any = true;
                        }
                        break;
                    }
                }

                // Generic "follow" sentinels where we should stop recovery.
                let at_follow = matches!(
                    kind,
                    TokenKind::EOF
                        | TokenKind::RightCurly
                        | TokenKind::RightParen
                        | TokenKind::Comma
                        | TokenKind::NewLine
                ) || Self::is_decl_start(&kind);

                if at_follow {
                    // If we have not consumed anything yet and we're parked *on* the follow
                    // token, consume exactly one token to guarantee forward progress.
                    if !consumed_any && !self.is_eof() {
                        let tok = self.lex.token();
                        last_end = tok.span.end;
                        consumed_any = true;
                    }
                    break;
                }

                // Special case: if we see a semicolon, consume it and stop.
                if matches!(kind, TokenKind::Semi) {
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
        let mut consumed_any = false;

        while !self.is_eof() {
            let kind = self.peek_kind();
            if depth == 0 {
                // Respect an explicit stop token from the caller.
                if let Some(stop) = stop_token {
                    if kind.similar_to(stop) {
                        if !consumed_any && !self.is_eof() {
                            let _ = self.lex.token();
                        }
                        break;
                    }
                }

                // Follow set for comma‑separated lists and bracketed sequences.
                // When we hit one of these, consume exactly one token to ensure
                // forward progress and then stop.
                if matches!(
                    kind,
                    TokenKind::Comma
                        | TokenKind::RightCurly
                        | TokenKind::RightParen
                        | TokenKind::RightBracket
                        | TokenKind::NewLine
                ) {
                    if !consumed_any && !self.is_eof() {
                        let _ = self.lex.token();
                    }
                    break;
                }
            }

            let tok = self.lex.token();
            consumed_any = true;
            match tok.kind {
                TokenKind::LeftParen | TokenKind::LeftBracket | TokenKind::LeftCurly => depth += 1,
                TokenKind::RightParen | TokenKind::RightBracket | TokenKind::RightCurly => {
                    if depth == 0 {
                        // We've found a closing delimiter at top level of the sequence; keep it
                        // consumed (progress!) and stop so the caller can handle it.
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
        let mut parsed = Parsed::new(TyScheme::from_mono(Ty::Never), self.mk_src(span));
        let id = self.mk_synthetic(span);
        parsed.set_synthetic_ids(vec![id]);
        parsed
    }

    fn parse_type_annotation(
        &mut self,
        stop: Option<&TokenKind>,
        ctx: &ParseContext,
    ) -> Parsed<TyScheme> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("parsing type annotation");
        let ctx = &parser.ctx_clone();
        let start = parser.lex.position();
        let next_kind = parser.peek_kind();
        let should_short_circuit = stop
            .map(|stop_kind| next_kind.similar_to(stop_kind))
            .unwrap_or(false);

        if should_short_circuit {
            let peek_token = parser.lex.peek_token().clone();
            let err = parser.unexpected_token(&peek_token, "type", ctx);
            parser.record_parse_error(err);
            return parser.missing_type(start, peek_token.span.start);
        }

        parser.parse_ty(ctx).recover_with_ctx(
            parser,
            RecoveryCtx::expr(stop).with_ternary_sensitive(false),
            |parser, recovered| parser.missing_type(start, recovered),
        )
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
                self.record_trivia(TriviaKind::Comment, c.span, None);
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
        // let start = self.lex.position();
        let (leading, tok) = self.lex.consume();
        for trivia in leading {
            if let Preceding::Comment(comment_tok) = trivia {
                self.record_trivia(TriviaKind::Comment, comment_tok.span, None);
            }
        }
        Ok(tok)
    }

    fn peek(&mut self) -> Token {
        self.lex.peek_token().clone()
    }

    fn peek_kind(&mut self) -> TokenKind {
        self.lex.peek_token().kind.clone()
    }

    fn peek_kind_at(&mut self, idx: usize) -> TokenKind {
        self.lex.peek_token_at(idx).kind.clone()
    }

    fn must_peek_kind(&mut self) -> ParseResult<TokenKind> {
        Ok(self.peek_kind())
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

    /// True if there is a statement boundary
    fn at_stmt_boundary(&mut self) -> bool {
        self.is_eol() || matches!(self.peek_kind(), TokenKind::NewLine | TokenKind::Semi)
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

    pub(crate) fn mk_synthetic(&mut self, span: Span) -> NodeId {
        let mut rng = rand::thread_rng();
        let id = NodeId(rng.next_u64());
        let src = Source {
            span: Some(span),
            filepath: self.options.filepath.clone(),
            src_module: self.options.module_path.clone(),
            ..Default::default()
        };
        self.srcmap.set_src_id(id, src);
        id
    }

    pub(crate) fn mk_src(&self, span: Span) -> Source {
        Source {
            filepath: self.options.filepath.clone(),
            span: Some(span),
            src_module: self.options.module_path.clone(),
            ..Default::default()
        }
    }

    pub(crate) fn record_trivia(
        &mut self,
        kind: TriviaKind,
        span: Span,
        token_kind: Option<TokenKind>,
    ) {
        self.srcmap
            .record_trivia(&self.options.filepath, kind, span, token_kind);
    }

    fn expect(&mut self, kind: TokenKind, ctx: &ParseContext) -> ParseResult<Token> {
        let tok = self.token()?;
        if tok.kind.similar_to(&kind) {
            Ok(tok)
        } else {
            Err(self.unexpected_token(&tok, kind.desc(), ctx))
        }
    }

    fn expect_string(&mut self, ctx: &ParseContext) -> ParseResult<(String, Span)> {
        let parser = &mut self.with_scope(ctx).with_description("string literal");
        let ctx = &parser.ctx_clone();
        let start = parser.expect_start(TokenKind::DoubleQuote, ctx)?;
        let (s, terminated) = parser.lex.quoted_string('"');
        let end = parser.lex.position();
        if !terminated {
            return Err(parser.unexpected_eof(end, "unterminated string literal".to_string()));
        }

        Ok((s, Span { start, end }))
    }

    fn expect_char(&mut self, ctx: &ParseContext) -> ParseResult<(String, Span)> {
        let parser = &mut self.with_scope(ctx).with_description("character literal");
        let ctx = &parser.ctx_clone();
        let start = parser.expect_start(TokenKind::SingleQuote, ctx)?;
        let (s, terminated) = parser.lex.quoted_string('\'');
        let end = parser.lex.position();
        if !terminated {
            return Err(parser.unexpected_eof(end, "unterminated character literal".to_string()));
        }

        Ok((s, Span { start, end }))
    }

    fn expect_ty_var_ident(&mut self, ctx: &ParseContext) -> ParseResult<(String, Span)> {
        let parser = &mut self
            .with_scope(ctx)
            .with_description("type variable identifier");
        let ctx = &parser.ctx_clone();
        let start = parser.expect_start(TokenKind::SingleQuote, ctx)?;
        let (mut ident, Span { end, .. }) = parser.expect_id(ctx)?;
        ident.insert(0, '\'');
        Ok((ident, Span { start, end }))
    }

    fn expect_id(&mut self, ctx: &ParseContext) -> ParseResult<(String, Span)> {
        let parser = &mut self.with_scope(ctx).with_description("expect identifier");
        let ctx = &parser.ctx_clone();
        let tok = parser.peek();
        match tok.kind {
            TokenKind::Identifier(_) | TokenKind::Struct | TokenKind::Underscore => {
                let tok = parser.token()?;
                let span = tok.span;
                Ok((tok.kind.to_string(), span))
            }
            _ => Err(parser.unexpected_token(&tok, "identifier", ctx)),
        }
    }

    fn expect_sp(&mut self, kind: TokenKind, ctx: &ParseContext) -> ParseResult<Span> {
        let tok = self.token()?;
        if tok.kind.similar_to(&kind) {
            Ok(tok.span)
        } else {
            Err(self.unexpected_token(&tok, kind.desc(), ctx))
        }
    }

    fn expect_keyword(&mut self, kind: TokenKind, ctx: &ParseContext) -> ParseResult<Span> {
        let span = self.expect_sp(kind.clone(), ctx)?;
        self.record_trivia(TriviaKind::Keyword, span, Some(kind));
        Ok(span)
    }

    fn expect_one_of(
        &mut self,
        kinds: &[TokenKind],
        trivia_kind: Option<TriviaKind>,
        ctx: &ParseContext,
    ) -> ParseResult<Option<Token>> {
        for kind in kinds {
            if self.peek_kind() == *kind {
                let tok = self.expect(kind.clone(), ctx)?;
                if let Some(trivia_kind) = trivia_kind {
                    self.record_trivia(trivia_kind, tok.span, Some(kind.clone()));
                }
                return Ok(Some(tok));
            }
        }

        Ok(None)
    }

    fn expect_if_operator(&mut self, kind: TokenKind) -> ParseResult<Option<Token>> {
        let tok = self.peek();
        if tok.kind.similar_to(&kind) {
            let tok = self.token()?;
            self.record_trivia(TriviaKind::Operator, tok.span, Some(tok.kind.clone()));
            Ok(Some(tok))
        } else {
            Ok(None)
        }
    }

    fn expect_start(&mut self, kind: TokenKind, ctx: &ParseContext) -> ParseResult<Pos> {
        Ok(self.expect_sp(kind, ctx)?.start)
    }

    fn expect_end(&mut self, kind: TokenKind, ctx: &ParseContext) -> ParseResult<Pos> {
        Ok(self.expect_sp(kind, ctx)?.end)
    }

    fn expect_semi_or_eol(&mut self, ctx: &ParseContext) -> ParseResult<Pos> {
        log::debug!(
            "[parser] expect_semi_or_eol: next={:?} is_eol={} pos={:?}",
            self.peek_kind(),
            self.is_eol(),
            self.lex.position()
        );
        match self.peek_kind() {
            TokenKind::NewLine | TokenKind::Semi => {
                let mut tok = self.token()?;
                let mut start = tok.span.start;
                log::debug!(
                    "[parser] expect_semi_or_eol: consuming {:?} at {:?}",
                    tok.kind,
                    tok.span
                );
                while matches!(self.peek_kind(), TokenKind::NewLine | TokenKind::Semi) {
                    tok = self.token()?;
                    start = tok.span.start;
                    log::debug!(
                        "[parser] expect_semi_or_eol: consuming {:?} at {:?}",
                        tok.kind,
                        tok.span
                    );
                }
                Ok(start)
            }
            _ => {
                let tok = self.peek();
                Err(self.unexpected_token(&tok, "`;` or a new line", ctx))
            }
        }
    }

    fn expect_matching(
        &mut self,
        start: &Token,
        end: TokenKind,
        ctx: &ParseContext,
    ) -> ParseResult<Pos> {
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
                ctx,
            ));
        }

        self.expect_end(end, ctx)
    }

    fn consume_newlines(&mut self, ctx: &ParseContext) -> ParseResult<()> {
        while matches!(self.peek_kind(), TokenKind::NewLine) {
            self.expect(TokenKind::NewLine, ctx)?;
        }
        Ok(())
    }

    /// Determine if the lexer is currently at the end of a line
    /// First, we peek the next token with the preceding whitespace
    /// and comments if there is a newline token in the preceding,
    /// then the lexer must be at the end of the current line
    fn is_eol(&mut self) -> bool {
        matches!(self.peek_kind(), TokenKind::NewLine)
            || self.is_eof()
            || self.lex.peek_preceding().iter().any(|p| match p {
                Preceding::Whitespace(t) | Preceding::Comment(t) => {
                    t.kind == TokenKind::NewLine || t.span.lines() > 1
                }
            })
    }

    fn parse_error(&self, msg: String, span: Span, ctx: &ParseContext) -> RayError {
        RayError {
            msg,
            src: vec![Source {
                span: Some(span),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Parse,
            context: ctx.description.clone(),
        }
    }

    fn unexpected_eof(&mut self, start: Pos, context: String) -> RayError {
        let end = self.lex.position();
        RayError {
            msg: format!("unexpected end of file"),
            src: vec![Source {
                span: Some(Span { start, end }),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::Parse,
            context: Some(context),
        }
    }

    fn unexpected_token(&self, tok: &Token, expected: &str, ctx: &ParseContext) -> RayError {
        let span = if let Some(anchor) = ctx.anchor {
            Span {
                start: anchor,
                end: tok.span.end,
            }
        } else {
            tok.span
        };
        RayError {
            msg: format!("expected {}, but found `{}`", expected, tok),
            src: vec![Source {
                span: Some(span),
                filepath: self.options.filepath.clone(),
                ..Default::default()
            }],
            kind: RayErrorKind::UnexpectedToken,
            context: ctx.description.clone(),
        }
    }
}
