//! Functions over bytes their caller owns, compiled from Heather.
//!
//! `count_newlines` (`lib/native/native_tool_spans.hthr`) is a `runtime fn`
//! whose first parameter is a span of bytes: it reads the caller's memory
//! where it lies, through a pointer and a length, and copies nothing. Its
//! certificate says what that takes (the crate's comment), and the
//! generated wrapper is where a `&[u8]` gives it; nothing here is `unsafe`.
//!
//! Every read is under the span's own length word: the function compares
//! an index with the length it was passed before it loads, so a count past
//! the end reads nothing past it (the Heather function counts a byte there
//! as none, and the code is proved to compute the Heather function).
//!
//! `raise_span` in the same module stores into its span: each byte from an
//! index to below a count is raised to upper case where it is a lower-case
//! ASCII letter, and stored back. Its certificate says the span holds the
//! Heather function's bytes after the call and nothing else the caller
//! owns has changed; the wrapper takes a `&mut [u8]`. A store is under the
//! length word as a read is, so a count past the end stores nothing past
//! it.
//!
//! `copy_span` is lent two spans, one to write and one to read: it stores
//! into the first what it reads of the second, index by index. Its
//! certificate asks that the two lie apart, which a `&mut [u8]` beside a
//! `&[u8]` is, and says the span read is as it was. Each span has its own
//! length word: nothing is stored past the end of the written one, and a
//! byte past the end of the one read is read nowhere and stored as zero.

use crate::exports;

/// How many of `text`'s first `count` bytes are newlines; a byte past the
/// end of `text` counts as none.
#[inline]
pub fn count_newlines(text: &[u8], count: u64) -> u64 {
    exports::count_newlines(text, count)
}

/// How many newlines `text` has.
#[inline]
pub fn newlines(text: &[u8]) -> u64 {
    exports::count_newlines(text, text.len() as u64)
}

/// `text`'s bytes from `from` to below `count` raised to upper case where
/// they are lower-case ASCII letters, in place; a byte past the end of
/// `text` is neither read nor stored. Answers the index it stopped at:
/// `count`, or `from` where that is not below it.
#[inline]
pub fn raise_span(text: &mut [u8], count: u64, from: u64) -> u64 {
    exports::raise_span(text, count, from)
}

/// `text`'s lower-case ASCII letters raised to upper case, in place.
#[inline]
pub fn raise(text: &mut [u8]) {
    exports::raise_span(text, text.len() as u64, 0);
}

/// `text`'s bytes from `from` to below `count` stored at their own indices
/// in `out`; `text` is not changed. Nothing is stored past the end of
/// `out`, and where `text` has ended the byte stored is zero. Answers the
/// index it stopped at: `count`, or `from` where that is not below it.
#[inline]
pub fn copy_span(out: &mut [u8], text: &[u8], count: u64, from: u64) -> u64 {
    exports::copy_span(out, text, count, from)
}

/// As much of `text` as `out` holds, copied to the start of `out`: how many
/// bytes that was.
#[inline]
pub fn copy(out: &mut [u8], text: &[u8]) -> usize {
    let count = out.len().min(text.len());
    exports::copy_span(out, text, count as u64, 0);
    count
}
