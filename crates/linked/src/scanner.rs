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

/// A token's kind, numbered as `lexer_scan.hthr`'s `KIND_*` constants are
/// (the test `the_kinds_are_the_modules` reads them from the source). The
/// names are `heather_syntax::TokKind`'s, with the two kinds a scanner has
/// and a lexer drops: [`Kind::Space`] and [`Kind::Comment`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
#[rustfmt::skip]
pub enum Kind {
    Ident = 1, Num = 2, Scaled = 3, Char = 4, Str = 5, ArgSlot = 6, Hole = 7, LParen = 8,
    RParen = 9, LBrace = 10, RBrace = 11, Comma = 12, Colon = 13, Semi = 14, At = 15, Dot = 16,
    Plus = 17, Minus = 18, Bang = 19, PlusPlus = 20, Star = 21, Lt = 22, LtEq = 23, Gt = 24,
    LBracket = 25, RBracket = 26, LSemantic = 27, RSemantic = 28, LAngle = 29, RAngle = 30,
    Pipe = 31, Amp = 32, Slash = 33, Percent = 34, Shl = 35, Shr = 36, Arrow = 37, FatArrow = 38,
    Turnstile = 39, AmpAmp = 40, PipePipe = 41, NormBar = 42, Bullet = 43, Approx = 44, Caret = 45,
    SupInverse = 46, Join = 47, Meet = 48, Neg = 49, Wedge = 50, Vee = 51, Iff = 52, LArrow = 53,
    Exists = 54, BigSum = 55, BigProd = 56, UpArrow = 57, Forall = 58, Dollar = 59, Lambda = 60,
    Eq = 61, Ne = 62, EqEq = 63, ColonEq = 64, ColonColon = 65, Eof = 66, Space = 67, Comment = 68,
    OPlus = 69, Tilde = 70,
}

impl Kind {
    /// Every kind, in code order: `ALL[k as usize - 1] == k`.
    #[rustfmt::skip]
    pub const ALL: [Kind; 70] = [
        Kind::Ident, Kind::Num, Kind::Scaled, Kind::Char, Kind::Str, Kind::ArgSlot, Kind::Hole,
        Kind::LParen, Kind::RParen, Kind::LBrace, Kind::RBrace, Kind::Comma, Kind::Colon, Kind::Semi,
        Kind::At, Kind::Dot, Kind::Plus, Kind::Minus, Kind::Bang, Kind::PlusPlus, Kind::Star, Kind::Lt,
        Kind::LtEq, Kind::Gt, Kind::LBracket, Kind::RBracket, Kind::LSemantic, Kind::RSemantic,
        Kind::LAngle, Kind::RAngle, Kind::Pipe, Kind::Amp, Kind::Slash, Kind::Percent, Kind::Shl,
        Kind::Shr, Kind::Arrow, Kind::FatArrow, Kind::Turnstile, Kind::AmpAmp, Kind::PipePipe,
        Kind::NormBar, Kind::Bullet, Kind::Approx, Kind::Caret, Kind::SupInverse, Kind::Join,
        Kind::Meet, Kind::Neg, Kind::Wedge, Kind::Vee, Kind::Iff, Kind::LArrow, Kind::Exists,
        Kind::BigSum, Kind::BigProd, Kind::UpArrow, Kind::Forall, Kind::Dollar, Kind::Lambda, Kind::Eq,
        Kind::Ne, Kind::EqEq, Kind::ColonEq, Kind::ColonColon, Kind::Eof, Kind::Space, Kind::Comment,
        Kind::OPlus, Kind::Tilde,
    ];

    /// The kind with this code, if it is one.
    pub fn of_code(code: u64) -> Option<Kind> {
        let index = usize::try_from(code).ok()?.checked_sub(1)?;
        Kind::ALL.get(index).copied()
    }

    /// The code the automaton accepts this kind with.
    pub fn code(self) -> u64 {
        self as u64
    }
}

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

/// How many of a token word's low bits are the token's end; its kind is
/// above them.
const END_BITS: u32 = 56;

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
#[inline]
pub fn token(source: &[u8], at: usize, previous: u64) -> Option<(u64, usize)> {
    let word = exports::scan_token(source, at as u64, previous);
    if word == 0 {
        return None;
    }
    Some((word >> END_BITS, (word & ((1 << END_BITS) - 1)) as usize))
}
