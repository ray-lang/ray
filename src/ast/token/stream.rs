// use crate::ast::token::{Delim, Token, TokenKind, TokenTree};
// use crate::parse::Lexer;

// pub struct TokenStream {
//     trees: Vec<TokenTree>,
// }

// impl TokenStream {
//     pub fn with_lexer(lexer: &mut Lexer) -> TokenStream {
//         let mut stream = TokenStream { trees: Vec::new() };
//         stream.get_trees(lexer);
//         stream
//     }

//     pub fn get_trees(&mut self, lexer: &mut Lexer) -> Option<()> {
//         let r = lexer.token();
//         let tok = r.token?;
//         match tok.kind {
//             TokenKind::LeftBracket | TokenKind::LeftCurly | TokenKind::LeftParen => {
//                 self.get_tree(lexer, Delim::Open(tok))?;
//             }
//             TokenKind::RightBracket | TokenKind::RightCurly | TokenKind::RightParen => {}
//             _ => {
//                 self.get_tree(lexer, Delim::Empty)?;
//             }
//         };
//         None
//     }

//     fn get_tree(&mut self, lexer: &mut Lexer, delim: Delim) -> Option<()> {
//         let tree = TokenTree::new(delim);
//         self.trees.push(tree);
//         loop {
//             let r = lexer.token();
//             if let Some(tok) = r.token {
//                 match tok.kind {
//                     TokenKind::LeftBracket | TokenKind::LeftCurly | TokenKind::LeftParen => {
//                         self.get_tree(lexer, Delim::Open(tok))?;
//                     }
//                     TokenKind::RightBracket | TokenKind::RightCurly | TokenKind::RightParen => {
//                         tree.tokens.push(tok);
//                         break;
//                     }
//                     _ => tree.tokens.push(tok),
//                 };
//             } else {
//                 break;
//             }
//         }
//         Some(())
//     }
// }
