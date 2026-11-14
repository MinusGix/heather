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
//! (`scan_token_longest`). [`Scanner`] calls [`token`] once for each
//! token, drops whitespace and comments, and hands out the tokens as an
//! iterator. [`records`] is that loop too, in Heather: one linked call
//! (`scan_tokens` of `lexer_records.hthr`) stores the kept tokens into a
//! span the caller lends, sixteen bytes each, proved to be the
//! specification's (`scan_tokens_records`); [`tokens_by_records`] reads
//! them back. Nothing in this file decides anything the automaton does not.
//!
//! # A scanner, not a lexer
//!
//! A [`Token`] is a kind and a span. What the Rust lexer's tokens also hold
//! (a numeral's value, a string with its escapes resolved) is a function of
//! the span, computed apart (`docs/native-lexer-crypto-roadmap.md` §3), and
//! with it the three refusals that are about a value and not a shape: an
//! exponent past a machine integer, a `\u{…}` that is not a scalar value,
//! and an argument-slot index past a machine word. Every other refusal of
//! `heather_syntax::lex` is a refusal here, with its reason
//! (`heather_syntax::lexer::ScanRefusal`, numbered as the module's
//! `REFUSED_*`) and the offset it is refused at, which are all the lexer's
//! message needs; `tests/scanner.rs` holds the two to each other on every
//! file of the library, messages included.

use crate::constants::{REFUSAL_AT_BITS, TOKEN_END_BITS};
use crate::exports;

/// What [`step`] is given after the last byte, and for any word that is not
/// a byte: every state stops or refuses on it.
pub const END: u64 = 256;

/// The state with no way on: the token is the last one accepted, and the
/// scan refuses if there was none.
pub const DEAD: u64 = 0;

/// The number of a state that refuses: a refusal no earlier accept can
/// excuse (`12abc`, an unterminated string). Its reason is the bits above
/// the number, where an accepting state has its kind: [`failed`],
/// [`accept`].
pub const FAIL: u64 = 2;

/// Whether a state refuses.
#[inline]
pub fn failed(state: u64) -> bool {
    state & 0xff == FAIL
}

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

/// The kind of the token that ends in this state, or zero; in a state that
/// refuses, the reason.
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

/// A refusal: where the token that could not be scanned starts, the
/// reason's code (`lexer_scan.hthr`'s `REFUSED_*`), and the offset it was
/// refused at.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Refused {
    pub start: usize,
    pub reason: u64,
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
            let (kind, end) = match token(self.source, start, self.previous) {
                Ok((code, end)) => match Kind::of_code(code) {
                    Some(kind) => (kind, end),
                    None => unreachable!("the automaton accepts no kind numbered {code}"),
                },
                Err((reason, at)) => {
                    self.finished = true;
                    return Some(Err(Refused { start, reason, at }));
                }
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
/// it ends; or the refusal, its reason's code and the offset it was refused
/// at: the byte that took the automaton to [`FAIL`], the source's length
/// where [`END`] did, or `at` where it stopped having accepted nothing.
///
/// This is `scan_token` of `lexer_span.hthr`, the whole loop in one call:
/// the automaton runs from [`begin`]`(previous)` until it stops, and is
/// given [`END`] once after the last byte. It answers one word: the kind
/// above the end, or zero above the reason above the offset, which no
/// token's word is (a kind is not zero). An offset fits its bits: a span
/// is lent below 2^47.
///
/// The word is read apart as `token_word_kind`, `token_word_end` and
/// `refusal_word_parts` of `lexer_span.hthr` read it back;
/// [`TOKEN_END_BITS`] and [`REFUSAL_AT_BITS`] are the module's own,
/// generated.
#[inline]
pub fn token(source: &[u8], at: usize, previous: u64) -> Result<(u64, usize), (u64, usize)> {
    read_word(exports::scan_token(source, at as u64, previous))
}

/// A token's word or a refusal's, read apart.
#[inline]
fn read_word(word: u64) -> Result<(u64, usize), (u64, usize)> {
    let kind = word >> TOKEN_END_BITS;
    if kind == 0 {
        return Err(((word >> REFUSAL_AT_BITS) & 0xff, (word & ((1 << REFUSAL_AT_BITS) - 1)) as usize));
    }
    Ok((kind, (word & ((1 << TOKEN_END_BITS) - 1)) as usize))
}

/// The bytes of a record [`records`] stores: the offset a token starts at,
/// then its word as [`token`] answers it, each a big-endian `u64`.
pub const RECORD_BYTES: usize = 16;

/// The tokens of `source` from `at`, after a token of kind `previous`,
/// stored into `out` as records, and how many: one for each token that is
/// kept (not whitespace, not a comment), then one for the end of the file
/// at the source's length or for the refusal that stops the scan. Where
/// `out` has no room for the next record the loop stops, and the scan goes
/// on from the end of the last record, after a token of its kind.
///
/// This is `scan_tokens` of `lexer_records.hthr`: the whole token loop in
/// one call, proved to store the records the specification lists
/// (`scan_tokens_records`, over `Record::from`, which is `Scanned::from`
/// with the tokens before a refusal kept).
#[inline]
pub fn records(out: &mut [u8], source: &[u8], at: usize, previous: u64) -> usize {
    exports::scan_tokens(out, source, at as u64, previous) as usize
}

/// Record `i` of what [`records`] stored: where it starts, and its token's
/// kind and end or its refusal's reason and offset.
pub fn record(out: &[u8], i: usize) -> (usize, Result<(u64, usize), (u64, usize)>) {
    let at = i * RECORD_BYTES;
    let start = u64::from_be_bytes(out[at..at + 8].try_into().unwrap()) as usize;
    let word = u64::from_be_bytes(out[at + 8..at + 16].try_into().unwrap());
    (start, read_word(word))
}

/// Every token of a source by the linked token loop, `room` records a call
/// (at least one): what [`tokens`] answers, with the loop in Heather.
pub fn tokens_by_records(source: &[u8], room: usize) -> Result<Vec<Token>, Refused> {
    let mut out = vec![0u8; room.max(1) * RECORD_BYTES];
    let mut tokens = Vec::new();
    let (mut at, mut previous) = (0, 0);
    loop {
        let stored = records(&mut out, source, at, previous);
        for i in 0..stored {
            match record(&out, i) {
                (start, Err((reason, refused))) => return Err(Refused { start, reason, at: refused }),
                (start, Ok((code, end))) => {
                    let Some(kind) = Kind::of_code(code) else { unreachable!("the automaton accepts no kind numbered {code}") };
                    tokens.push(Token { kind, start, end });
                    if kind == Kind::Eof {
                        return Ok(tokens);
                    }
                    (at, previous) = (end, code);
                }
            }
        }
    }
}
