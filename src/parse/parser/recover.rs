use crate::errors::RayError;

use super::{Parser, Pos, TokenKind};

pub trait Recover<T> {
    fn recover_with(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>, Pos) -> T,
    ) -> T;

    fn recover_seq(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>) -> T,
    ) -> T;
}

impl<T> Recover<T> for Result<T, RayError> {
    fn recover_with(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>, Pos) -> T,
    ) -> T {
        match self {
            Ok(value) => value,
            Err(err) => {
                parser.record_parse_error(err);
                let recovered = parser.recover_after_error(stop);
                fallback(parser, recovered)
            }
        }
    }

    fn recover_seq(
        self,
        parser: &mut Parser<'_>,
        stop: Option<&TokenKind>,
        fallback: impl FnOnce(&mut Parser<'_>) -> T,
    ) -> T {
        match self {
            Ok(value) => value,
            Err(err) => {
                parser.record_parse_error(err);
                parser.recover_after_sequence_error(stop);
                fallback(parser)
            }
        }
    }
}
