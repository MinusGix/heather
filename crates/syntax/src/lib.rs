//! Surface syntax for Heather: lexer, parser, surface AST, spans/diagnostics.
//! Untrusted — everything here is elaborated into kernel terms and re-checked.
//!
//! Stage 1 subset (issues/elaborator-design.md, order of attack): `fn` and
//! `theorem` declarations, `Nat`, `==` (identity), numerals, calls, `match`
//! on Nat with the explicit-ih fallback patterns, `refl`, and `j` (path
//! induction). No metavariables, no level syntax (everything at level 0),
//! no quotes. The AST is the stable contract; the grammar is swappable
//! (docs/sketches/surface-v0..3.md).

pub mod ast;
pub mod lexer;
pub mod parser;

pub use ast::*;
pub use parser::{parse_file, ParseError};
