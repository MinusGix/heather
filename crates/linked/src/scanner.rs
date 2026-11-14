//! Heather's scanner: where each token of a source file starts and ends and
//! which kind it is, decided a byte at a time by compiled Heather.
//!
//! The automaton is `lib/lang/lexer/lexer_scan.hthr`: [`step`] moves a state
//! over one byte, [`accept`] reads the token a state completes, and
//! [`begin`] is the state a token starts in after the one before it.
//! [`token`] is the loop over them, the longest match with the last
//! accepting position remembered: `scan_token` of `lexer_span.hthr`, one
//! linked function that reads the source where it lies, through a pointer
//! and a length (`spans` says what lending takes). The same loop is written
//! in Heather as the specification (`lexer_tokens.hthr`, `Scanned::of`),
//! where the kernel evaluates it, and the linked one is proved to be it
//! (`scan_token_longest`). [`Scanner`] is what is left in Rust: it calls
//! [`token`] once for each token, drops whitespace and comments, and makes
//! the values an iterator hands out, which a compiled function cannot write
//! into its caller's memory yet (`issues/native-library-exports-design.md`).
//! Nothing in this file decides anything the automaton does not.
//!
//! # A scanner, not a lexer
//!
//! A [`Token`] is a kind and a span. What the Rust lexer's tokens also hold
//! (a numeral's value, a string with its escapes resolved) is a function of
//! the span, computed apart (`docs/native-lexer-crypto-roadmap.md` §3), and
//! with it the three refusals that are about a value and not a shape: an
//! exponent past a machine integer, a `\u{…}` that is not a scalar value,
//! and an argument-slot index past a machine word. Every other refusal of
//! `heather_syntax::lex` is a refusal here, and `tests/scanner.rs` holds the
//! two to each other on every file of the library.

use crate::constants::TOKEN_END_BITS;
use crate::exports;

/// What [`step`] is given after the last byte, and for any word that is not
/// a byte: every state stops or refuses on it.
pub const END: u64 = 256;

/// The state with no way on: the token is the last one accepted, and the
/// scan refuses if there was none.
pub const DEAD: u64 = 0;

/// The state of a refusal no earlier accept can excuse (`12abc`, an
/// unterminated string).
pub const FAIL: u64 = 2;

/// One byte in a state. The low eight bits of a state name it and the bits
/// above them are the kind it accepts, zero for none.
///
/// This is `scan_step` of `lexer_scan.hthr`, one export: the states come in
/// families, each family is a function, and the compiled program holds
/// them all with the function that chooses among them, linked in Heather
/// (`scan_step::agrees`) and certified as one program.
#[inline]
pub fn step(state: u64, byte: u64) -> u64 {
    exports::scan_step(state, byte)
}

/// The kind of the token that ends in this state, or zero.
#[inline]
pub fn accept(state: u64) -> u64 {
    exports::scan_accept(state)
}

/// The state a token starts in, given the kind of what came before it (zero
/// at the start of the source): `>>` is a shift only at the start, after
/// whitespace, after `(` and after `,`.
#[inline]
pub fn begin(previous: u64) -> u64 {
    exports::scan_begin(previous)
}

// A token's kind, `Kind`: the names are `heather_syntax::TokKind`'s, with
// the two kinds a scanner has and a lexer drops (`Kind::Space`,
// `Kind::Comment`), and the codes are `lexer_scan.hthr`'s `KIND_*`. Written
// from the table `TOKEN_KINDS` (`lib/lang/lexer/lexer_kinds.hthr`) by
// `scripts/linked`, as the Rust lexer's `ScanKind` is: one file, so neither
// crate numbers a kind by hand.
include!("../generated/kinds.rs");

/// A token: its kind, and the bytes `start..end` of the source.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub kind: Kind,
    pub start: usize,
    pub end: usize,
}

/// A refusal: the offset of the token that could not be scanned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Refused {
    pub at: usize,
}

/// The tokens of a source in order, whitespace and comments dropped, ending
/// in an [`Kind::Eof`] at its length; or the refusal, after which there is
/// nothing more. `Scanned::of` of `lexer_tokens.hthr`.
pub struct Scanner<'a> {
    source: &'a [u8],
    at: usize,
    /// The kind of what was scanned last, zero at the start.
    previous: u64,
    finished: bool,
}

impl<'a> Scanner<'a> {
    pub fn new(source: &'a [u8]) -> Scanner<'a> {
        Scanner { source, at: 0, previous: 0, finished: false }
    }
}

impl Iterator for Scanner<'_> {
    type Item = Result<Token, Refused>;

    fn next(&mut self) -> Option<Result<Token, Refused>> {
        if self.finished {
            return None;
        }
        while self.at < self.source.len() {
            let start = self.at;
            let scanned = token(self.source, start, self.previous).and_then(|(code, end)| Some((Kind::of_code(code)?, end)));
            let Some((kind, end)) = scanned else {
                self.finished = true;
                return Some(Err(Refused { at: start }));
            };
            self.previous = kind.code();
            self.at = end;
            if !matches!(kind, Kind::Space | Kind::Comment) {
                return Some(Ok(Token { kind, start, end }));
            }
        }
        self.finished = true;
        Some(Ok(Token { kind: Kind::Eof, start: self.at, end: self.at }))
    }
}

/// Every token of a source, or its refusal.
pub fn tokens(source: &[u8]) -> Result<Vec<Token>, Refused> {
    Scanner::new(source).collect()
}

/// The longest token of `source` from `at`, after a token of kind
/// `previous` (zero at the start of the source): its kind's code and where
/// it ends. `None` is a refusal: the automaton refused, or stopped having
/// accepted nothing.
///
/// This is `scan_token` of `lexer_span.hthr`, the whole loop in one call:
/// the automaton runs from [`begin`]`(previous)` until it stops, and is
/// given [`END`] once after the last byte. It answers one word, the kind
/// above the end, and zero for a refusal, which no token's word is (a kind
/// is not zero). An end fits its bits: a span is lent below 2^47.
///
/// The word is read apart as `token_word_kind` and `token_word_end` of
/// `lexer_span.hthr` read it back, and `token_word_nonzero` is why zero is
/// only a refusal; [`TOKEN_END_BITS`] is the module's own, generated.
#[inline]
pub fn token(source: &[u8], at: usize, previous: u64) -> Option<(u64, usize)> {
    let word = exports::scan_token(source, at as u64, previous);
    if word == 0 {
        return None;
    }
    Some((word >> TOKEN_END_BITS, (word & ((1 << TOKEN_END_BITS) - 1)) as usize))
}
