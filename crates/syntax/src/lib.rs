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
mod within;

pub use ast::*;
pub use parser::{class_ty, leading_imports, written_paths, operator_form, parse_file, pos_carrier, OperatorForm, ParseError, BY_TACTIC, MUTATED_RECORD, POS_RESULT, POS_SEARCH};
pub use fmt::format_source;
pub use roles::{argument_lists, token_roles, ArgumentLists, Delims, TokenRole};

pub use try_lower::{expr_children_mut, without_decrease_labels};
pub use try_lower::{BIND_SEQ, ITERATE_THEN, POINTED_RET};
pub use within::{WITHIN, WITHIN_FOR};
pub use imperative::{AFTER, BRK, LOOP, MUTATED, MUTATED_AFTER, MUTATED_VALUE, MUTATED_WHOLE, MUTARG, MUTCALL, NEXT, PATHCALL, PROJ, RET, STATE, WHILE};
pub use imperative::{place_root, place_update};
