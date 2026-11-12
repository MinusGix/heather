//! The linked functions over a span, against plain Rust, and the process
//! controls of the contract they are called under.
//!
//! `heather_linked::spans::count_newlines` is compiled Heather reading the
//! caller's bytes through a pointer and a length
//! (docs/native-library-exports-design.md), `scanner::token` is the
//! scanner's loop the same way, with calls of compiled code inside it, and
//! `spans::raise_span` stores into the bytes it is lent. A certificate says
//! the code computes the Heather function, reads only the span it is lent
//! and stores only into its own stack room and a span lent to write; what
//! it cannot reach is the platform around the call, and these are the
//! checks on that side (§6 of the design, clauses 1, 3, 4, 5 and 7):
//!
//! - against a reference, on texts of every length and counts on both sides
//!   of the length, and on every Heather source in the repository (the
//!   scanner's reference is `tests/scanner.rs`);
//! - a span that ends where the next page is unmapped, read at its length
//!   and past it, and an empty slice, whose pointer dangles: no fault and
//!   the reference's answer, with the kernel asked to confirm that the byte
//!   after the span cannot be read;
//! - a written span with an unmapped page on each side, and one inside a
//!   larger buffer: nothing is stored outside the span, whatever the count;
//! - a function lent one span to write and one to read (`spans::copy_span`):
//!   the same of the written span, and the span read ending at an unmapped
//!   page, read to its length and no further;
//! - the code entered at both stack alignments, with the callee-saved
//!   registers compared across the call.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]
// Mapping a page and entering the code at a chosen alignment are what the
// controls are; the crate's `deny` is for what it ships.
#![allow(unsafe_code)]

use std::path::{Path, PathBuf};

use heather_linked::{scanner, spans};

/// The same count in plain Rust.
fn reference(text: &[u8], count: u64) -> u64 {
    text.iter().take(usize::try_from(count).unwrap_or(usize::MAX)).filter(|byte| **byte == b'\n').count() as u64
}

/// Bytes with newlines among them, from a fixed seed.
fn bytes(length: usize, seed: u64) -> Vec<u8> {
    let mut state = seed | 1;
    (0..length).map(|_| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        // One byte in four a newline, the rest anything.
        if state & 3 == 0 { b'\n' } else { (state >> 8) as u8 }
    }).collect()
}

#[test]
fn counts_as_the_reference() {
    for length in (0..70).chain([255, 256, 257, 4095, 4096, 4097]) {
        let text = bytes(length, 0x9e37_79b9_7f4a_7c15 ^ length as u64);
        // Every count up to the length, and past it: a byte past the end
        // counts as none and is not read.
        for count in (0..=length as u64 + 3).chain([length as u64 + 4096, 1 << 20]) {
            assert_eq!(spans::count_newlines(&text, count), reference(&text, count), "length {length}, count {count}");
        }
        assert_eq!(spans::newlines(&text), reference(&text, length as u64), "length {length}");
    }
    // Every byte value is told from a newline.
    let every: Vec<u8> = (0..=255).collect();
    assert_eq!(spans::newlines(&every), 1);
    assert_eq!(spans::newlines(&[b'\n'; 1000]), 1000);
}

fn sources_under(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries {
        let path = entry.expect("entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "target") { continue; }
            sources_under(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "hthr") {
            out.push(path);
        }
    }
}

// The library's own sources: megabytes of text through a loop that keeps
// one frame.
#[test]
fn counts_the_lines_of_every_source() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut sources = Vec::new();
    sources_under(&root.join("lib"), &mut sources);
    assert!(sources.len() > 100, "the library was not found");
    let mut whole = Vec::new();
    for path in &sources {
        let text = std::fs::read(path).expect("source");
        assert_eq!(spans::newlines(&text), reference(&text, text.len() as u64), "{}", path.display());
        whole.extend_from_slice(&text);
    }
    assert_eq!(spans::newlines(&whole), reference(&whole, whole.len() as u64));
}

/// A Linux system call, raw: the controls map pages and need nothing else.
fn syscall(number: u64, arguments: [u64; 6]) -> i64 {
    let result: i64;
    // SAFETY: the `syscall` instruction with the kernel's register
    // convention; what each call does is its caller's to justify.
    unsafe {
        core::arch::asm!("syscall", inlateout("rax") number as i64 => result, in("rdi") arguments[0], in("rsi") arguments[1],
            in("rdx") arguments[2], in("r10") arguments[3], in("r8") arguments[4], in("r9") arguments[5],
            lateout("rcx") _, lateout("r11") _, options(nostack));
    }
    result
}

const PAGE: usize = 4096;
const WRITE: u64 = 1;
const MMAP: u64 = 9;
const MPROTECT: u64 = 10;
const MUNMAP: u64 = 11;
const EFAULT: i64 = -14;

/// Three pages, the first and the last neither readable nor writable: a
/// span that ends at `boundary` has nothing after it, and one that starts
/// at `start` nothing before it.
struct Guarded { base: usize }

impl Guarded {
    fn new() -> Guarded {
        // PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS.
        let base = syscall(MMAP, [0, 3 * PAGE as u64, 3, 0x22, u64::MAX, 0]);
        assert!(base > 0, "mmap: {base}");
        let guarded = Guarded { base: base as usize };
        assert_eq!(syscall(MPROTECT, [guarded.base as u64, PAGE as u64, 0, 0, 0, 0]), 0, "mprotect");
        assert_eq!(syscall(MPROTECT, [guarded.boundary() as u64, PAGE as u64, 0, 0, 0, 0]), 0, "mprotect");
        guarded
    }

    fn start(&self) -> usize { self.base + PAGE }

    fn boundary(&self) -> usize { self.base + 2 * PAGE }

    /// `text` copied so that its last byte is the last readable one.
    fn ending_at_the_boundary(&mut self, text: &[u8]) -> &mut [u8] {
        assert!(text.len() <= PAGE);
        self.holding(self.boundary() - text.len(), text)
    }

    /// `text` copied so that its first byte is the first readable one.
    fn starting_at_the_start(&mut self, text: &[u8]) -> &mut [u8] {
        assert!(text.len() <= PAGE);
        self.holding(self.start(), text)
    }

    fn holding(&mut self, at: usize, text: &[u8]) -> &mut [u8] {
        // SAFETY: `at..at + text.len()` is inside the middle page, which
        // this owns and mapped writable, and the slice borrows `self`; an
        // empty text makes an empty slice at a non-null address.
        unsafe {
            std::ptr::copy_nonoverlapping(text.as_ptr(), at as *mut u8, text.len());
            std::slice::from_raw_parts_mut(at as *mut u8, text.len())
        }
    }
}

impl Drop for Guarded {
    fn drop(&mut self) {
        syscall(MUNMAP, [self.base as u64, 3 * PAGE as u64, 0, 0, 0, 0]);
    }
}

// Clause 5: the code reads only the span. The byte after it is one the
// kernel itself refuses to read (the control on the control), and the code
// is given every chance to: a count at the length and well past it.
#[test]
fn a_span_at_an_unmapped_page_is_read_to_its_end_only() {
    let mut pages = Guarded::new();
    // A pipe: the kernel copies what is written to it, so it reads the
    // bytes (a write to `/dev/null` reads nothing).
    let (_reader, writer) = std::io::pipe().expect("pipe");
    let fd = std::os::fd::AsRawFd::as_raw_fd(&writer) as u64;
    assert_eq!(syscall(WRITE, [fd, pages.boundary() as u64, 1, 0, 0, 0]), EFAULT, "the page after the span is readable");
    for length in [0, 1, 2, 7, 8, 9, 63, 64, 65, 1000, PAGE] {
        let text = bytes(length, 0xdead_beef ^ length as u64);
        let boundary = pages.boundary();
        let span = pages.ending_at_the_boundary(&text);
        assert_eq!(span.as_ptr() as usize + span.len(), boundary);
        assert_eq!(syscall(WRITE, [fd, span.as_ptr() as u64, span.len() as u64, 0, 0, 0]), length as i64, "the span itself is readable");
        for count in [0, length as u64 / 2, length as u64, length as u64 + 1, length as u64 + 8, length as u64 + 2 * PAGE as u64] {
            assert_eq!(spans::count_newlines(span, count), reference(&text, count), "length {length}, count {count}");
        }
    }
}

// An empty slice's pointer is dangling: nothing is read through it,
// whatever the count.
#[test]
fn an_empty_slice_is_read_nowhere() {
    let empty: &[u8] = &[];
    let none: Vec<u8> = Vec::new();
    for text in [empty, &none[..], &b"\n\n\n"[3..]] {
        for count in [0, 1, 8, 4096] {
            assert_eq!(spans::count_newlines(text, count), 0, "count {count}");
        }
    }
}

// The scanner's loop reads to the end of its span and stops there: a token
// that runs to the last byte (a name, a comment with no newline, a string
// never closed) is where a read past the length would be, and the byte
// after it is not there to read. The answer is the one the same code gives
// for the same bytes anywhere else (that it is the right one is
// `tests/scanner.rs`).
#[test]
fn a_token_at_an_unmapped_page_is_scanned_to_the_spans_end_only() {
    let mut pages = Guarded::new();
    for text in ["", "a", "abc", "x1 // to the end", "\"never closed", "12", "a >>", "nat::Nat", "0x1.8p", "1.", "λ", "a\n", "::"] {
        let text = text.as_bytes();
        let boundary = pages.boundary();
        let span = pages.ending_at_the_boundary(text);
        assert_eq!(span.as_ptr() as usize + span.len(), boundary);
        // From every offset, and from past the end, where nothing is read.
        for at in (0..=text.len() + 1).chain([text.len() + PAGE, 2 * PAGE + 7, usize::MAX]) {
            for previous in [0, scanner::Kind::Ident.code()] {
                assert_eq!(scanner::token(span, at, previous), scanner::token(text, at, previous), "{:?} from {at}", String::from_utf8_lossy(text));
            }
        }
    }
    // A page that is one token: every byte of the span is read and none
    // after it.
    let page = [b'a'; PAGE];
    let span = pages.ending_at_the_boundary(&page);
    assert_eq!(scanner::token(span, 0, 0), Some((scanner::Kind::Ident.code(), PAGE)));
    assert_eq!(scanner::token(span, PAGE - 1, 0), Some((scanner::Kind::Ident.code(), PAGE)));
    assert_eq!(scanner::token(span, PAGE, 0), None);
}

/// What `raise_span` leaves and answers, in plain Rust: the bytes from
/// `from` to below `count` that the text has, raised, and the index the
/// loop stopped at.
fn raised(text: &[u8], count: u64, from: u64) -> (Vec<u8>, u64) {
    let mut after = text.to_vec();
    let end = usize::try_from(count).unwrap_or(usize::MAX).min(text.len());
    let start = usize::try_from(from).unwrap_or(usize::MAX);
    if start < end { after[start..end].make_ascii_uppercase(); }
    (after, from.max(count))
}

// Clause 2 and the write half's post: the word answered and the bytes the
// span holds after are the reference's, on texts of every length, from
// every kind of start and to counts on both sides of the length.
#[test]
fn raises_as_the_reference() {
    for length in (0..70).chain([255, 256, 257, 4095, 4096, 4097]) {
        // Letters of both cases among any bytes.
        let text: Vec<u8> = bytes(length, 0x7a5e ^ length as u64).iter().enumerate()
            .map(|(i, byte)| match i % 3 { 0 => b'a' + byte % 26, 1 => b'A' + byte % 26, _ => *byte }).collect();
        let length = length as u64;
        for count in [0, 1, length / 2, length.saturating_sub(1), length, length + 1, length + 9, length + 4096] {
            for from in [0, 1, length / 3, length, length + 2, count, count + 1] {
                let mut span = text.clone();
                let answered = spans::raise_span(&mut span, count, from);
                assert_eq!((span, answered), raised(&text, count, from), "length {length}, count {count}, from {from}");
            }
        }
        let mut span = text.clone();
        spans::raise(&mut span);
        assert_eq!(span, text.to_ascii_uppercase(), "length {length}");
    }
    // Every byte value: the twenty-six lower-case letters move and nothing
    // else does.
    let every: Vec<u8> = (0..=255).collect();
    let mut span = every.clone();
    spans::raise(&mut span);
    assert_eq!(span, every.to_ascii_uppercase());
    assert_eq!(span.iter().zip(&every).filter(|(after, before)| after != before).count(), 26);
}

// Clause 4 with a span lent to write: the code stores into the span and
// nowhere else the caller owns. Here the span is part of a larger buffer,
// and the bytes on both sides of it are letters a store would raise.
#[test]
fn nothing_is_stored_outside_the_span() {
    for (before, length, after) in [(0, 0, 16), (1, 1, 1), (7, 9, 5), (64, 100, 64), (3, 4096, 3)] {
        let whole = vec![b'q'; before + length + after];
        for count in [0, length as u64 / 2, length as u64, length as u64 + 1, (before + length + after) as u64 + 64] {
            let mut buffer = whole.clone();
            let answered = spans::raise_span(&mut buffer[before..before + length], count, 0);
            assert_eq!(answered, count, "length {length}, count {count}");
            let raised = usize::try_from(count).unwrap().min(length);
            assert!(buffer[..before].iter().all(|byte| *byte == b'q'), "a byte before the span changed: length {length}, count {count}");
            assert!(buffer[before..before + raised].iter().all(|byte| *byte == b'Q'), "length {length}, count {count}");
            assert!(buffer[before + raised..].iter().all(|byte| *byte == b'q'), "a byte past the count changed: length {length}, count {count}");
        }
    }
}

// The same at the edge of what can be written at all: the pages on both
// sides of the span take no store (the kernel confirms neither can be
// read, and a store there would be a fault here), and the code is given a
// count well past the span's end and a start before nothing.
#[test]
fn a_written_span_between_unmapped_pages_is_stored_to_its_ends_only() {
    let mut pages = Guarded::new();
    let (_reader, writer) = std::io::pipe().expect("pipe");
    let fd = std::os::fd::AsRawFd::as_raw_fd(&writer) as u64;
    assert_eq!(syscall(WRITE, [fd, pages.boundary() as u64, 1, 0, 0, 0]), EFAULT, "the page after the span is readable");
    assert_eq!(syscall(WRITE, [fd, pages.start() as u64 - 1, 1, 0, 0, 0]), EFAULT, "the page before the span is readable");
    for length in [0, 1, 2, 7, 8, 9, 63, 64, 65, 1000, PAGE] {
        let text: Vec<u8> = bytes(length, 0xfeed ^ length as u64).iter().map(|byte| b'a' + byte % 26).collect();
        for count in [0, length as u64 / 2, length as u64, length as u64 + 1, length as u64 + 8, length as u64 + 2 * PAGE as u64] {
            for from in [0, length as u64 / 2, length as u64, length as u64 + 1] {
                let expected = raised(&text, count, from);
                let boundary = pages.boundary();
                let span = pages.ending_at_the_boundary(&text);
                assert_eq!(span.as_ptr() as usize + span.len(), boundary);
                let answered = spans::raise_span(span, count, from);
                assert_eq!((span.to_vec(), answered), expected, "ending at the boundary: length {length}, count {count}, from {from}");
                let start = pages.start();
                let span = pages.starting_at_the_start(&text);
                assert_eq!(span.as_ptr() as usize, start);
                let answered = spans::raise_span(span, count, from);
                assert_eq!((span.to_vec(), answered), expected, "starting at the start: length {length}, count {count}, from {from}");
            }
        }
    }
    // A whole page between the two, every byte of it stored.
    let page = [b'z'; PAGE];
    let span = pages.ending_at_the_boundary(&page);
    assert_eq!(spans::raise_span(span, 3 * PAGE as u64, 0), 3 * PAGE as u64);
    assert!(span.iter().all(|byte| *byte == b'Z'));
}

// An empty slice's pointer is dangling: nothing is stored through it.
#[test]
fn an_empty_slice_is_stored_nowhere() {
    let empty: &mut [u8] = &mut [];
    for count in [0, 1, 8, 4096] {
        assert_eq!(spans::raise_span(empty, count, 0), count);
    }
    let mut none: Vec<u8> = Vec::new();
    assert_eq!(spans::raise_span(&mut none, 64, 3), 64);
}

/// What `copy_span` leaves in `out` and answers, in plain Rust: each index
/// from `from` to below `count` that `out` has takes `text`'s byte there,
/// or zero where `text` has ended.
fn copied(out: &[u8], text: &[u8], count: u64, from: u64) -> (Vec<u8>, u64) {
    let mut after = out.to_vec();
    let end = usize::try_from(count).unwrap_or(usize::MAX).min(out.len());
    let start = usize::try_from(from).unwrap_or(usize::MAX);
    if start < end {
        for (i, byte) in after[start..end].iter_mut().enumerate() { *byte = text.get(start + i).copied().unwrap_or(0); }
    }
    (after, from.max(count))
}

// Two spans, one written and one read: the bytes the written one holds
// after and the word answered are the reference's, at every pairing of
// lengths (the read span shorter, equal and longer), counts on both sides
// of both lengths and starts on both sides of the count. The span read is
// borrowed shared, so that it is unchanged is the borrow's; it is compared
// all the same, since the code is the compiler's and not rustc's.
#[test]
fn copies_as_the_reference() {
    for out_length in (0..20usize).chain([63, 64, 65, 255, 4096, 4097]) {
        for text_length in [0, 1, out_length / 2, out_length.saturating_sub(1), out_length, out_length + 1, out_length + 70] {
            let out = bytes(out_length, 0xc0de ^ out_length as u64);
            let text = bytes(text_length, 0x7e87 ^ (text_length as u64) << 16 ^ out_length as u64);
            let (long, short) = (out_length.max(text_length) as u64, out_length.min(text_length) as u64);
            for count in [0, 1, short / 2, short, short + 1, long, long + 1, long + 4096] {
                for from in [0, 1, short / 3, short, count, count + 1] {
                    let mut span = out.clone();
                    let read = text.clone();
                    let answered = spans::copy_span(&mut span, &read, count, from);
                    assert_eq!((span, answered), copied(&out, &text, count, from), "out {out_length}, text {text_length}, count {count}, from {from}");
                    assert_eq!(read, text, "the span read changed: out {out_length}, text {text_length}, count {count}, from {from}");
                }
            }
            let mut span = out.clone();
            let count = spans::copy(&mut span, &text);
            assert_eq!(count, out_length.min(text_length));
            assert_eq!(span[..count], text[..count], "out {out_length}, text {text_length}");
            assert_eq!(span[count..], out[count..], "out {out_length}, text {text_length}");
        }
    }
}

// Clause 4 with two spans: the written one is part of a larger buffer and
// the one read is part of another; no byte outside the written span
// changes in either, whatever the count.
#[test]
fn a_copy_stores_into_the_written_span_only() {
    for (before, length, after) in [(0, 0, 16), (1, 1, 1), (7, 9, 5), (64, 100, 64), (3, 4096, 3)] {
        let whole = vec![b'q'; before + length + after];
        let source = vec![b'S'; before + length + after];
        for count in [0, length as u64 / 2, length as u64, length as u64 + 1, (before + length + after) as u64 + 64] {
            let mut buffer = whole.clone();
            let read = source.clone();
            let answered = spans::copy_span(&mut buffer[before..before + length], &read[before..before + length], count, 0);
            assert_eq!(answered, count, "length {length}, count {count}");
            let stored = usize::try_from(count).unwrap().min(length);
            assert!(buffer[..before].iter().all(|byte| *byte == b'q'), "a byte before the span changed: length {length}, count {count}");
            assert!(buffer[before..before + stored].iter().all(|byte| *byte == b'S'), "length {length}, count {count}");
            assert!(buffer[before + stored..].iter().all(|byte| *byte == b'q'), "a byte past the count changed: length {length}, count {count}");
            assert_eq!(read, source, "the buffer read changed: length {length}, count {count}");
        }
    }
}

// Both spans at the edge of what can be touched at all: the written one
// with an unmapped page on each side, the one read ending where the next
// page is unmapped (the kernel confirms neither page can be read). A count
// past both ends stores to the written span's end and reads to the read
// span's, and a fault would be a fault here.
#[test]
fn a_copy_between_unmapped_pages_touches_its_spans_only() {
    let mut written = Guarded::new();
    let mut read = Guarded::new();
    let (_reader, writer) = std::io::pipe().expect("pipe");
    let fd = std::os::fd::AsRawFd::as_raw_fd(&writer) as u64;
    for pages in [&written, &read] {
        assert_eq!(syscall(WRITE, [fd, pages.boundary() as u64, 1, 0, 0, 0]), EFAULT, "the page after the span is readable");
        assert_eq!(syscall(WRITE, [fd, pages.start() as u64 - 1, 1, 0, 0, 0]), EFAULT, "the page before the span is readable");
    }
    for out_length in [0, 1, 7, 8, 9, 64, 1000, PAGE] {
        for text_length in [0, 1, out_length / 2, out_length, (out_length + 9).min(PAGE)] {
            let out = bytes(out_length, 0xfeed ^ out_length as u64);
            let text = bytes(text_length, 0xbeef ^ text_length as u64);
            let long = out_length.max(text_length) as u64;
            for count in [0, long / 2, long, long + 1, long + 2 * PAGE as u64] {
                for from in [0, long / 2, long + 1] {
                    let expected = copied(&out, &text, count, from);
                    let boundary = read.boundary();
                    let source: &[u8] = read.ending_at_the_boundary(&text);
                    assert_eq!(source.as_ptr() as usize + source.len(), boundary);
                    let span = written.ending_at_the_boundary(&out);
                    let answered = spans::copy_span(span, source, count, from);
                    assert_eq!((span.to_vec(), answered), expected, "ending at the boundary: out {out_length}, text {text_length}, count {count}, from {from}");
                    assert_eq!(source, &text[..], "the span read changed: out {out_length}, text {text_length}, count {count}, from {from}");
                    let source: &[u8] = read.starting_at_the_start(&text);
                    let span = written.starting_at_the_start(&out);
                    let answered = spans::copy_span(span, source, count, from);
                    assert_eq!((span.to_vec(), answered), expected, "starting at the start: out {out_length}, text {text_length}, count {count}, from {from}");
                }
            }
        }
    }
}

// Empty slices on either side dangle: nothing is read or stored through
// them.
#[test]
fn a_copy_of_or_into_an_empty_slice() {
    let empty: &mut [u8] = &mut [];
    for count in [0, 1, 8, 4096] {
        assert_eq!(spans::copy_span(empty, b"text", count, 0), count);
        assert_eq!(spans::copy_span(empty, &[], count, 0), count);
        let mut out = *b"four";
        assert_eq!(spans::copy_span(&mut out, &[], count, 0), count);
        // Where the text has ended the byte stored is zero.
        let stored = (count as usize).min(4);
        assert!(out[..stored].iter().all(|byte| *byte == 0) && out[stored..] == b"four"[stored..], "count {count}");
    }
}

unsafe extern "sysv64" {
    // The code itself, as `generated/exports.rs` declares it privately.
    fn copy_span(out: *mut u8, out_length: u64, text: *const u8, text_length: u64, count: u64, from: u64) -> u64;
    fn count_newlines(text: *const u8, length: u64, count: u64) -> u64;
    fn raise_span(text: *mut u8, length: u64, count: u64, from: u64) -> u64;
    fn scan_token(source: *const u8, length: u64, at: u64, previous: u64) -> u64;
}

/// Sentinels for the callee-saved registers an operand may name (RBX and
/// RBP are the compiler's own; it would fail in its own way were they
/// lost).
const KEPT: [u64; 4] = [0x1212_1212_1212_1212, 0x1313_1313_1313_1313, 0x1414_1414_1414_1414, 0x1515_1515_1515_1515];

/// `$code` entered with RSP moved down by `$pad` bytes first: `0` is the
/// platform's alignment and `8` the other one. `$text` is the span and
/// `$third`, `$fourth` the words after it (a function of fewer is given a
/// word it does not read). Returns the result and the callee-saved
/// registers as the code left them. The `@at` form takes the span as its
/// pointer and length, for a span the code stores into.
macro_rules! entered {
    ($pad:literal, $code:ident, $text:expr, $third:expr, $fourth:expr) => {{
        let text: &[u8] = $text;
        entered!(@at $pad, $code, text.as_ptr(), text.len() as u64, $third, $fourth)
    }};
    (@at $pad:literal, $code:ident, $pointer:expr, $length:expr, $third:expr, $fourth:expr) => {{
        let (pointer, length) = ($pointer, $length);
        let result: u64;
        let (r12, r13, r14, r15): (u64, u64, u64, u64);
        // SAFETY: the premises of the function's `_native_returns`, as the
        // generated wrapper states them, for the span; RSP is moved inside the
        // block and put back before it ends, and the block is not `nostack`,
        // so nothing of this function lives below it.
        unsafe {
            core::arch::asm!(
                concat!("sub rsp, ", $pad),
                "call {code}",
                concat!("add rsp, ", $pad),
                code = sym $code,
                in("rdi") pointer, in("rsi") length, in("rdx") $third, in("rcx") $fourth,
                inout("r12") KEPT[0] => r12, inout("r13") KEPT[1] => r13, inout("r14") KEPT[2] => r14, inout("r15") KEPT[3] => r15,
                out("rax") result,
                clobber_abi("sysv64"),
            );
        }
        (result, [r12, r13, r14, r15])
    }};
}

/// The same for a function of six words, two spans and two words after
/// them: every argument register the platform has.
macro_rules! entered_six {
    ($pad:literal, $code:ident, $out:expr, $out_length:expr, $text:expr, $count:expr, $from:expr) => {{
        let (out, out_length) = ($out, $out_length);
        let text: &[u8] = $text;
        let result: u64;
        let (r12, r13, r14, r15): (u64, u64, u64, u64);
        // SAFETY: as `entered!`; the two spans are apart, the first writable
        // and the second readable for the call.
        unsafe {
            core::arch::asm!(
                concat!("sub rsp, ", $pad),
                "call {code}",
                concat!("add rsp, ", $pad),
                code = sym $code,
                in("rdi") out, in("rsi") out_length, in("rdx") text.as_ptr(), in("rcx") text.len() as u64, in("r8") $count, in("r9") $from,
                inout("r12") KEPT[0] => r12, inout("r13") KEPT[1] => r13, inout("r14") KEPT[2] => r14, inout("r15") KEPT[3] => r15,
                out("rax") result,
                clobber_abi("sysv64"),
            );
        }
        (result, [r12, r13, r14, r15])
    }};
}

// Clause 7: no premise of the certificate mentions the stack's alignment,
// so the code is right at both. Clause 3 on the way: the callee-saved
// registers come back.
#[test]
fn both_stack_alignments() {
    for length in [0, 1, 17, 300, 5000] {
        let text = bytes(length, 0x5eed ^ length as u64);
        for count in [0, length as u64, length as u64 + 5] {
            let expected = reference(&text, count);
            assert_eq!(entered!(0, count_newlines, &text, count, 0u64), (expected, KEPT), "length {length}, count {count}, the platform's alignment");
            assert_eq!(entered!(8, count_newlines, &text, count, 0u64), (expected, KEPT), "length {length}, count {count}, RSP eight lower");
        }
    }
}

// The same of the scanner's loop, whose code calls the automaton's: what
// it calls is compiled code under the same contract, so the alignment it
// was entered at is the one its callees see, and none of them reads it.
#[test]
fn the_scanners_loop_at_both_stack_alignments() {
    for text in ["", "abc def", "x // to the end", "\"s\" 1.5e3 >> :: λ", "12abc"] {
        let text = text.as_bytes();
        for at in 0..=text.len() as u64 + 1 {
            for previous in [0, scanner::Kind::Ident.code()] {
                // The word `scanner::token` reads apart: the kind above the end.
                let expected = scanner::token(text, at as usize, previous).map_or(0, |(kind, end)| kind << 56 | end as u64);
                let what = String::from_utf8_lossy(text);
                assert_eq!(entered!(0, scan_token, text, at, previous), (expected, KEPT), "{what:?} from {at}, the platform's alignment");
                assert_eq!(entered!(8, scan_token, text, at, previous), (expected, KEPT), "{what:?} from {at}, RSP eight lower");
            }
        }
    }
}

// And of the writer: the bytes it leaves and the word it answers are the
// reference's at both alignments, with the callee-saved registers back.
#[test]
fn the_writer_at_both_stack_alignments() {
    for length in [0, 1, 17, 300, 5000] {
        let text: Vec<u8> = bytes(length, 0xa11e ^ length as u64).iter().map(|byte| b'a' + byte % 26).collect();
        for (count, from) in [(0, 0), (length as u64, 0), (length as u64 + 5, 1), (length as u64 / 2, length as u64)] {
            let expected = raised(&text, count, from);
            let mut span = text.clone();
            let answered = entered!(@at 0, raise_span, span.as_mut_ptr(), span.len() as u64, count, from);
            assert_eq!((span, answered), (expected.0.clone(), (expected.1, KEPT)), "length {length}, count {count}, the platform's alignment");
            let mut span = text.clone();
            let answered = entered!(@at 8, raise_span, span.as_mut_ptr(), span.len() as u64, count, from);
            assert_eq!((span, answered), (expected.0, (expected.1, KEPT)), "length {length}, count {count}, RSP eight lower");
        }
    }
}

// And of the function lent two spans, which takes all six argument
// registers.
#[test]
fn the_copy_at_both_stack_alignments() {
    for length in [0, 1, 17, 300, 5000] {
        let out = bytes(length, 0x0a11 ^ length as u64);
        let text = bytes(length + 3, 0x7e47 ^ length as u64);
        for (count, from) in [(0, 0), (length as u64, 0), (length as u64 + 5, 1), (length as u64 / 2, length as u64)] {
            let expected = copied(&out, &text, count, from);
            let mut span = out.clone();
            let answered = entered_six!(0, copy_span, span.as_mut_ptr(), span.len() as u64, &text, count, from);
            assert_eq!((span, answered), (expected.0.clone(), (expected.1, KEPT)), "length {length}, count {count}, the platform's alignment");
            let mut span = out.clone();
            let answered = entered_six!(8, copy_span, span.as_mut_ptr(), span.len() as u64, &text, count, from);
            assert_eq!((span, answered), (expected.0, (expected.1, KEPT)), "length {length}, count {count}, RSP eight lower");
        }
    }
}
