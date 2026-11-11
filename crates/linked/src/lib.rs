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
//! stores nowhere but in its own room below the return address
//! (`Stack::Wrote`), so the caller's stack and everything else it owns are
//! as they were. That is the System V
//! contract for a function of words, which is why the declarations below are
//! `safe fn`: nothing a caller passes can make the call misbehave.
//!
//! An export may also read **a span of bytes its caller owns**
//! (docs/native-library-exports-design.md): its code takes the span's
//! address and length as two words, and its `_returns` theorem has the
//! premises a pointer needs, that the two words are a span of readable
//! bytes the callee's own stores cannot reach (`Stack::LentOver`, `Loan`),
//! and then says as well that the span is left as it was. A `&[u8]` meets
//! those premises, so the function Rust sees takes one: the declaration
//! over a pointer is `unsafe` and private, and the wrapper that calls it
//! with a slice's parts is generated with the premises beside the call
//! (`generated/exports.rs`). No export stores into a span yet.
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
//!
//! [`spans`]: the first export that reads memory its caller owns, a count
//! of a text's newlines (`lib/native/native_tool_spans.hthr`). Its tests
//! are the contract's process controls: a span that ends at an unmapped
//! page, an empty slice, and both stack alignments.

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod scanner;
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod spans;
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod sha256;
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
pub mod sha512;

// The one module the crate's `unsafe_code = "deny"` is lifted for: linking
// the compiler's bytes and naming the functions in them. It is generated in
// full (`scripts/linked`, from `generated/EXPORTS.tsv` and the signature
// each assembly file states), and `crates/cli/tests/linked_exports.rs`
// refuses a hand edit to it.
#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
#[allow(unsafe_code)]
#[path = "../generated/exports.rs"]
mod exports;
