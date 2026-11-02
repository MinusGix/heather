//! Surface syntax for Heather: lexer, parser, surface AST, spans/diagnostics.
//! Untrusted — everything here is elaborated into kernel terms and re-checked.
//!
//! Current subset (issues/elaborator-design.md, order of attack): `fn` and
//! `theorem` declarations, `inductive` declarations with type parameters,
//! `Nat` and declared types, `=` (identity), numerals, calls, `match` with
//! one arm per constructor (`Nat`'s `Succ(k, ih)` remains the explicit-ih
//! fallback), `refl`, `j` (path induction), holes and `on` discharges. No
//! level syntax (everything at level 0), no quotes. The AST is the stable
//! contract; the grammar is swappable (docs/sketches/surface-v0..3.md).

pub mod ast;
pub mod fmt;
pub mod lexer;
pub mod parser;
pub mod roles;
mod try_lower;
mod imperative;

pub use ast::*;
pub use parser::{class_ty, parse_file, pos_carrier, ParseError, BY_TACTIC, POS_RESULT, POS_SEARCH};
pub use fmt::format_source;
pub use roles::{argument_lists, token_roles, ArgumentLists, Delims, TokenRole};

pub use try_lower::without_decrease_labels;
pub use try_lower::{BIND_SEQ, POINTED_RET};
pub use imperative::{AFTER, BRK, LOOP, NEXT, PROJ, RET, STATE, WHILE};
