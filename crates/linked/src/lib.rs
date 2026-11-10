//! Heather code, compiled by `heather compile-x86` and linked into Rust.
//!
//! This is the first place the workspace runs code Heather compiled *inside
//! a Rust program*, called directly, with no process between them
//! (`docs/native-lexer-crypto-roadmap.md`: both of that roadmap's targets
//! are libraries, a compiled function over memory its caller owns). What is
//! linked is `generated/*.s`: the bytes `compile-x86` certified, checked in,
//! and held to the compiler by `crates/cli/tests/native_linked.rs`, which
//! recompiles every export and compares. A build needs no Heather compiler.
//!
//! # What a linked function promises
//!
//! Each export is a `runtime fn` over 64-bit words. Its certificate's
//! `_returns` theorem (`examples/x86-native/README.md`) says: called at its
//! label with its arguments in RDI, RSI, RDX, RCX, R8, R9, a return address
//! at RSP and room on the stack below it, the code returns the source
//! function's value in RAX, keeps the callee-saved registers and RSP, and
//! leaves the stack above the return address as it was. That is the System V
//! contract for a function of words, which is why the declarations below are
//! `safe fn`: nothing a caller passes can make the call misbehave.
//!
//! What the theorem does not cover is stated where the compiler states it:
//! the platform around the call (that `extern "sysv64"` really passes
//! arguments so, that the stack has room, the assembler and the linker) is
//! outside the proof. The tests here are the check on that gap: every export
//! is run against the plain Rust for the same function.
//!
//! # What is here
//!
//! [`sha512`] and [`sha256`]: the word functions of the two compression
//! functions, and a whole hash over each. The words are Heather's
//! (`lib/native/crypto/sha512_round.hthr`, `sha256_round.hthr`, each proved
//! to be the specification's function, `lib/std/crypto/sha2.hthr`); the
//! eight working variables, the schedule's sixteen words, the constants and
//! the padding are Rust's, until the pure fragment holds arrays
//! (`issues/rt-fixed-arrays-and-tables.md`). SHA-256 is the compiler's own
//! hash (`crates/cache/src/sha256.rs`), and the tests here hold the linked
//! one to the oracle that one is held to; nothing shipped calls it yet
//! (`issues/sha256-linked-into-cache.md`).
//!
//! [`scanner`]: Heather's own scanner, the automaton that cuts a source file
//! into tokens (`lib/lang/lexer/lexer_scan.hthr`). Every decision about a
//! byte is the linked code's; the loop that hands it the bytes is Rust's,
//! for the same reason the hashes' state is. Its test holds it to the Rust
//! lexer on every Heather source in the repository; nothing shipped calls
//! it yet (`issues/self-lexer-linked.md`).

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod scanner;
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod sha256;
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod sha512;

// The one module the crate's `unsafe_code = "deny"` is lifted for: linking
// the compiler's bytes (`global_asm!`) and naming the functions in them.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[allow(unsafe_code)]
mod exports {
    // Each file is the compiler's output, verbatim (`options(raw)`: the text
    // is assembly, not a format string). It selects `.text` itself and ends
    // in a `.note.GNU-stack` section, so it is bracketed to leave the
    // assembler where it was.
    macro_rules! linked {
        ($file:literal) => {
            core::arch::global_asm!(
                ".pushsection .text",
                include_str!(concat!("../generated/", $file)),
                ".popsection",
                options(raw)
            );
        };
    }
    linked!("sha512_t1.s");
    linked!("sha512_t2.s");
    linked!("sha512_next.s");
    linked!("sha256_t1.s");
    linked!("sha256_t2.s");
    linked!("sha256_next.s");
    linked!("scan_family.s");
    linked!("scan_accept.s");
    linked!("scan_begin.s");

    // The scanner's state families (`scanner`'s comment): each is one file
    // and one function of a state and a byte, and `FAMILIES` holds them in
    // the order written here, which is `scan_families`' in
    // `lib/lang/lexer/lexer_scan.hthr` (the test `the_table_is_the_modules`
    // reads that list from the source).
    macro_rules! families {
        ($($name:ident),* $(,)?) => {
            $(
                core::arch::global_asm!(
                    ".pushsection .text",
                    include_str!(concat!("../generated/", stringify!($name), ".s")),
                    ".popsection",
                    options(raw)
                );
            )*
            unsafe extern "sysv64" {
                $( pub safe fn $name(state: u64, byte: u64) -> u64; )*
            }
            pub static FAMILIES: &[(&str, extern "sysv64" fn(u64, u64) -> u64)] = &[ $( (stringify!($name), $name) ),* ];
        };
    }
    families!(
        step_stop,
        step_start_space,
        step_start_punct,
        step_start_mid,
        step_start_high,
        step_trivia,
        step_names,
        step_arrows,
        step_doubles,
        step_decimal,
        step_fraction,
        step_octal,
        step_binary,
        step_hex,
        step_hex_fraction,
        step_hex_exponent,
        step_string,
        step_char,
        step_char_escape,
        step_two_byte,
        step_three_byte,
        step_symbols,
        step_logic,
    );

    // The functions are declared `safe` on the strength of their
    // certificates (the crate's comment): the unproved part is the
    // platform's, not the callee's.
    unsafe extern "sysv64" {
        pub safe fn sha512_t1(h: u64, e: u64, f: u64, g: u64, k: u64, w: u64) -> u64;
        pub safe fn sha512_t2(a: u64, b: u64, c: u64) -> u64;
        pub safe fn sha512_next(w2: u64, w7: u64, w15: u64, w16: u64) -> u64;
        // 32-bit words in the low halves (`sha256`'s comment).
        pub safe fn sha256_t1(h: u64, e: u64, f: u64, g: u64, k: u64, w: u64) -> u64;
        pub safe fn sha256_t2(a: u64, b: u64, c: u64) -> u64;
        pub safe fn sha256_next(w2: u64, w7: u64, w15: u64, w16: u64) -> u64;
        // The scanner's automaton around its families (`scanner`).
        pub safe fn scan_family(state: u64, byte: u64) -> u64;
        pub safe fn scan_accept(state: u64) -> u64;
        pub safe fn scan_begin(previous: u64) -> u64;
    }
}
