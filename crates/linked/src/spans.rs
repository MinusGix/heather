//! A function over bytes its caller owns, compiled from Heather.
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
