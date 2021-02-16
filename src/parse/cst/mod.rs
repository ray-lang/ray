use std::{fs, io};

use cst::{Char, Delimited, Delimiter};

use crate::{
    ast::token::{Token, TokenKind},
    cst::{self, Module, Node},
    errors::{RayError, RayErrorKind, RayResult},
    span::{parsed::Parsed, Pos, Source, Span},
};

use super::{Lexer, ParseOptions};

fn read_string<R: io::Read>(mut r: R) -> RayResult<String> {
    let mut src = String::new();
    r.read_to_string(&mut src)?;
    Ok(src)
}

pub struct Parser {
    lex: Lexer,
    options: ParseOptions,
}

impl Parser {
    pub fn parse(options: ParseOptions) -> RayResult<Module> {
        let src = Parser::get_src(&options)?;
        Parser::parse_from_src(src, options)
    }

    pub fn parse_from_src(src: String, options: ParseOptions) -> RayResult<Module> {
        let lex = Lexer::new(&src);
        let mut parser = Parser { lex, options };
        parser.parse_module()
    }

    fn get_src(options: &ParseOptions) -> RayResult<String> {
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

    fn is_eof(&mut self) -> bool {
        self.lex.peek_token().kind == TokenKind::EOF
    }

    fn token(&mut self) -> RayResult<Token> {
        let start = self.lex.position();
        let tok = self.lex.token();
        match tok.kind {
            TokenKind::EOF => Err(self.unexpected_eof(start)),
            _ => Ok(tok),
        }
    }

    fn span(&mut self) -> RayResult<Span> {
        let start = self.lex.position();
        let tok = self.lex.token();
        match tok.kind {
            TokenKind::EOF => Err(self.unexpected_eof(start)),
            _ => Ok(tok.span),
        }
    }

    fn src(&mut self) -> RayResult<Source> {
        let start = self.lex.position();
        let tok = self.lex.token();
        match tok.kind {
            TokenKind::EOF => Err(self.unexpected_eof(start)),
            _ => Ok(self.mk_src(tok.span)),
        }
    }

    fn mk_src(&mut self, span: Span) -> Source {
        Source {
            filepath: self.options.filepath.clone(),
            span: Some(span),
            ..Default::default()
        }
    }

    fn peek_kind(&mut self) -> &TokenKind {
        &self.lex.peek_token().kind
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

    fn parse_module(&mut self) -> RayResult<Module> {
        let path = self.options.module_path.clone();
        // let ctx = ParseContext::new(path.clone());
        let filepath = self.options.filepath.clone();
        let src = Source::from(filepath);
        let nodes = self.parse_nodes(|this| this.is_eof())?;
        let module = Module::new(path, src, nodes);
        Ok(module)
    }

    fn parse_nodes<F>(&mut self, mut cond: F) -> RayResult<Parsed<Node>>
    where
        F: FnMut(&mut Parser) -> bool,
    {
        let start = self.lex.position();
        let begin_delim = self.begin_delimiter()?;
        let mut nodes = vec![];
        while !cond(self) {
            nodes.push(self.parse_node()?);
        }
        let end_delim = begin_delim
            .as_ref()
            .map(|begin| self.end_delimiter(begin))
            .unwrap_or_else(|| Ok(None))?;
        let end = self.lex.position();
        let src = self.mk_src(Span { start, end });
        Ok(Parsed::new(
            Node::Delimited(Parsed::new(
                Delimited::new((begin_delim, end_delim), nodes),
                src.clone(),
            )),
            src,
        ))
    }

    fn parse_node(&mut self) -> RayResult<Parsed<Node>> {
        todo!()
    }

    fn parse_ident(&mut self) -> RayResult<Parsed<String>> {
        todo!()
    }

    fn begin_delimiter(&mut self) -> RayResult<Option<Parsed<Delimiter>>> {
        let delim = match self.peek_kind() {
            TokenKind::LeftParen => Delimiter::Paren,
            TokenKind::LeftCurly => Delimiter::Curly,
            TokenKind::LeftBracket => Delimiter::Bracket,
            TokenKind::SingleQuote => Delimiter::SingleQuote,
            TokenKind::DoubleQuote => Delimiter::DoubleQuote,
            _ => return Ok(None),
        };

        let src = self.src()?;
        Ok(Some(Parsed::new(delim, src)))
    }

    fn end_delimiter(&mut self, begin: &Delimiter) -> RayResult<Option<Parsed<Delimiter>>> {
        let delim = match self.peek_kind() {
            TokenKind::RightParen if matches!(begin, Delimiter::Paren) => Delimiter::Paren,
            TokenKind::RightCurly if matches!(begin, Delimiter::Curly) => Delimiter::Curly,
            TokenKind::RightBracket if matches!(begin, Delimiter::Bracket) => Delimiter::Bracket,
            TokenKind::SingleQuote if matches!(begin, Delimiter::SingleQuote) => {
                Delimiter::SingleQuote
            }
            TokenKind::DoubleQuote if matches!(begin, Delimiter::DoubleQuote) => {
                Delimiter::DoubleQuote
            }
            _ => return Ok(None),
        };

        let src = self.src()?;
        Ok(Some(Parsed::new(delim, src)))
    }

    fn special_char(&mut self) -> RayResult<Option<Parsed<Char>>> {
        todo!()
    }
}
