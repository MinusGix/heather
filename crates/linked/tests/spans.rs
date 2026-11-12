//! The linked functions over a span, against plain Rust, and the process
//! controls of the contract they are called under.
//!
//! `heather_linked::spans::count_newlines` is compiled Heather reading the
//! caller's bytes through a pointer and a length
//! (docs/native-library-exports-design.md), and `scanner::token` is the
//! scanner's loop the same way, with calls of compiled code inside it. A
//! certificate says the code computes the Heather function and reads only
//! the span it is lent; what it cannot reach is the platform around the
//! call, and these are the checks on that side (§6 of the design, clauses
//! 1, 3, 5 and 7):
//!
//! - against a reference, on texts of every length and counts on both sides
//!   of the length, and on every Heather source in the repository (the
//!   scanner's reference is `tests/scanner.rs`);
//! - a span that ends where the next page is unmapped, read at its length
//!   and past it, and an empty slice, whose pointer dangles: no fault and
//!   the reference's answer, with the kernel asked to confirm that the byte
//!   after the span cannot be read;
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

/// Two pages, the second one unreadable: a span that ends at `boundary`
/// has nothing after it.
struct Guarded { base: usize }

impl Guarded {
    fn new() -> Guarded {
        // PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS.
        let base = syscall(MMAP, [0, 2 * PAGE as u64, 3, 0x22, u64::MAX, 0]);
        assert!(base > 0, "mmap: {base}");
        let guarded = Guarded { base: base as usize };
        assert_eq!(syscall(MPROTECT, [guarded.boundary() as u64, PAGE as u64, 0, 0, 0, 0]), 0, "mprotect");
        guarded
    }

    fn boundary(&self) -> usize { self.base + PAGE }

    /// `text` copied so that its last byte is the last readable one.
    fn ending_at_the_boundary(&mut self, text: &[u8]) -> &[u8] {
        assert!(text.len() <= PAGE);
        let start = (self.boundary() - text.len()) as *mut u8;
        // SAFETY: `start..boundary` is inside the first page, which this
        // owns and mapped writable; an empty text makes an empty slice at a
        // non-null address.
        unsafe {
            std::ptr::copy_nonoverlapping(text.as_ptr(), start, text.len());
            std::slice::from_raw_parts(start, text.len())
        }
    }
}

impl Drop for Guarded {
    fn drop(&mut self) {
        syscall(MUNMAP, [self.base as u64, 2 * PAGE as u64, 0, 0, 0, 0]);
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

unsafe extern "sysv64" {
    // The code itself, as `generated/exports.rs` declares it privately.
    fn count_newlines(text: *const u8, length: u64, count: u64) -> u64;
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
/// registers as the code left them.
macro_rules! entered {
    ($pad:literal, $code:ident, $text:expr, $third:expr, $fourth:expr) => {{
        let text: &[u8] = $text;
        let result: u64;
        let (r12, r13, r14, r15): (u64, u64, u64, u64);
        // SAFETY: the premises of the function's `_native_returns`, as the
        // generated wrapper states them, for `text`; RSP is moved inside the
        // block and put back before it ends, and the block is not `nostack`,
        // so nothing of this function lives below it.
        unsafe {
            core::arch::asm!(
                concat!("sub rsp, ", $pad),
                "call {code}",
                concat!("add rsp, ", $pad),
                code = sym $code,
                in("rdi") text.as_ptr(), in("rsi") text.len() as u64, in("rdx") $third, in("rcx") $fourth,
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
