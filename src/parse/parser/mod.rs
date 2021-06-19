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
mod ty;

use std::{fs, io};

use crate::{
    ast::{
        token::{Token, TokenKind},
        Decl, Decorator, Expr, File, Import, Node, Path, ValueKind,
    },
    errors::{RayError, RayErrorKind},
    parse::lexer::{Lexer, Preceding},
    pathlib::FilePath,
    span::{parsed::Parsed, Pos, Source, SourceMap, Span},
    typing::ty::Ty,
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
    pub struct Restrictions: u8 {
        const EXPECT_EXPR   = 1 << 0;
        const IF_ELSE       = 1 << 1;
        const IN_LOOP       = 1 << 2;
        const IN_FUNC       = 1 << 3;
        const RVALUE        = 1 << 4;
        const NO_CURLY_EXPR = 1 << 5;
        const AFTER_COMMA   = 1 << 6;
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

#[derive(Clone, Debug)]
pub struct ParseOptions {
    pub module_path: Path,
    pub use_stdin: bool,
    pub filepath: FilePath,
    pub original_filepath: FilePath,
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
}

impl<'src> Parser<'src> {
    pub fn parse(options: ParseOptions, srcmap: &'src mut SourceMap) -> ParseResult<File> {
        let src = Self::get_src(&options)?;
        Self::parse_from_src(src, options, srcmap)
    }

    pub fn parse_from_src(
        src: String,
        options: ParseOptions,
        srcmap: &'src mut SourceMap,
    ) -> ParseResult<File> {
        let lex = Lexer::new(&src);
        let mut parser = Self {
            lex,
            options,
            srcmap,
        };
        parser.parse_into_file()
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
        let doc_comment = self.parse_doc_comment();
        let mut items = Items::new();
        let filepath = self.options.filepath.clone();
        let span = self.parse_items(Pos::new(), None, &ctx, |this, kind, doc, decs| {
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

        while !self.is_eof() {
            let doc = self.parse_doc_comment();
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

            end = f(self, kind, doc, decs)?;
        }

        Ok(Span { start, end })
    }

    fn parse_doc_comment(&mut self) -> Option<String> {
        let preceding = self.lex.preceding();
        if preceding.len() != 0 {
            let mut doc: Vec<String> = vec![];
            for p in preceding {
                if let Preceding::Comment(c) = p {
                    if let TokenKind::Comment {
                        content,
                        doc_style: true,
                    } = c.kind
                    {
                        doc.push(if let Some(' ') = content.chars().next() {
                            // skip the whitespace
                            content.chars().skip(1).collect()
                        } else {
                            content
                        });
                    }
                }
            }

            if doc.len() != 0 {
                Some(doc.join("\n"))
            } else {
                None
            }
        } else {
            None
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
        let (ident, Span { end, .. }) = self.expect_id()?;
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
