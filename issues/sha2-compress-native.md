---
title: SHA-2's compression function as a certified runtime fn
status: open
labels: [cryptography,native,x86,compiler]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-12
---

Stage C1 of `docs/native/native-lexer-crypto-roadmap.md` §4: SHA-2's compression
function as a `runtime fn`, compiled and certified, agreeing with
[[sha2-specification]]'s low-level form.

What master does today (probe `native-roadmap/sha_native.hthr`, 2026-11-10):
SHA-512's Σ0 as a `runtime fn` over `BitVec(64)` certifies through
`compile-x86` (66 bytes; each rotate is `MOV SHR MOV SHL OR`, and the leaf
reserves a 64-byte frame it never uses). SHA-256's Σ1 and T1 on 32-bit
words carried in 64-bit registers (`truncate`, 32-bit shifts,
`zero_extend`) reflect and agree, in 4 to 8 s each in the generator, and
`compile-x86` then refuses them: "the verified lowering refused this
program with the planner's placement" (`word_only`: widths 64 and 1).

## Scope

- The 64-bit instance first (SHA-512's compress), since it fits the
  lowering's width; the 32-bit instance when
  [[function-ir-narrow-arithmetic]] lands.
- The state and the schedule window as `[BitVec(w); n]`
  ([[rt-fixed-arrays-and-tables]]); the round as a loop of 64 or 80 passes
  over the constant table, not unrolled.
- `scripts/bench-probes` cases for one round body and for the whole
  compress, added before the function, so its certificate's cost is seen
  against [[function-ir-scan-id-cost]] and [[runtime-generator-link-cost]].
- A C harness over random blocks and the NIST long vectors, against
  `crates/cache/src/sha256.rs` ([[native-differential-harness]]).

## Done when

`compress` for SHA-512 and SHA-256 certifies, its agreement theorem
composes with the specification's to `compress = spec`, and the harness
passes.

## What it assumes from elsewhere

- **[[function-ir-multi-word-calls]]** or a buffer-held state: eight words
  in and out do not fit one result register.
- **[[runtime-default-setup-soundness]]** owns byte reads and writes.

## Log

- 2026-11-10: The arithmetic of both compression functions is compiled and proved; the memory is not. `lib/native/crypto/sha512_round.hthr` and `sha256_round.hthr` each hold three `runtime fn`s (`T1`, `T2`, one schedule word) with theorems taking them to [[sha2-specification]]: `sha512_round_spec` says a round of the specification is `Sha2State::turn` of the two compiled words, and `sha256_round_spec` the same through the 64-bit boundary (the specification's 32-bit word widened in, the low half of the result out). SHA-512's call a helper per Σ and σ; SHA-256's are one body each, since a call saves every live register and at this size that was most of the code. Certified sizes: SHA-512 `t1` 306 bytes with its two callees, SHA-256 `t1` 210 as one function, settles included. Both are linked into Rust and run as whole hashes with the state, schedule and constants held by the Rust caller (`crates/linked`, [[native-differential-harness]]). What this issue still owes is its actual scope: the state and schedule window as arrays, the round as a loop over the constant table, and `compress = spec` as one theorem ([[rt-fixed-arrays-and-tables]], [[native-library-exports-design]]). The bench-probe cases are not added yet.
- 2026-11-12: SHA-256's compress is whole as compiled code, over memory: `sha256_compress` in `lib/native/crypto/sha256_block.hthr`, a `runtime fn` lent a context it stores into and a block it reads, exported and linked (`heather_linked::sha256::block`). The buffer-held state this issue assumed is how it was done: the context is 320 bytes (hash value, working variables, schedule), since a function passes six words ([[function-call-past-six-words]]), and the constants are a tree of comparisons, since there is no table yet ([[rt-fixed-arrays-and-tables]]). The loops are measured recursions, one function each; the round is three functions so that each fits the planner. It certifies as one program. The harness is `crates/linked/tests/sha256.rs`: the NIST vectors and the long one, the `sha2` crate at every length through three blocks, the rounds written out in Rust from random hash values, and a transcription of the Heather function compared on every byte of the context for spans of every shorter length (nothing stored past an end, a short block read as zero-filled).

  Not done: `compress = spec`. Nothing connects `sha256_compress` to `Sha2::compress` but the tests. The pieces are `sha256_round`'s three theorems and the constants' (`constants_are_the_table`); the proof is an invariant per loop over the context's bytes, and it is hand-proved, so it waits on Minus. SHA-512's compress is not written; it is the same file at eight-byte words.

  Found on the way: [[runtime-link-compares-functions]] (fixed in the library, a rule still owed), [[runtime-measured-reader-heavy-callee]] (open, not on this path), [[bv-omega-binder-captures-t]].
- 2026-11-12: The hash is whole as compiled code: `sha256_init`, `sha256_update` and `sha256_finish` in `lib/native/crypto/sha256_stream.hthr`, over `sha256_block`'s context and eight more bytes for the count of bytes taken. The streaming update the issue's scope left open is in Heather, not Rust around `compress`: a block is assembled in the schedule's first sixteen words, a byte at a time, and run when the sixty-fourth lands (`sha256_push`, `sha256_absorb`), so a part that ends inside a block needs no carry buffer of its own; the padding is `sha256_pad` and `sha256_close`. `sha256_compress` is now `sha256_take_block` then `sha256_run`, the piece the stream shares. All three certify and are linked (`heather_linked::sha256::stream::Sha256`, the three calls `crates/cache`'s type has), tested against the `sha2` crate at every length through three blocks, at every split of a message in two round the block and padding boundaries, in varied parts, and on short spans. One thing the reflector asked for: a count read from the context before the stores and used after them has to be a parameter of a helper (`sha256_take`, `sha256_close`), [[rt-file-read-before-store]]. Still not proved against [[sha2-specification]], as above; the padding's proof would be against `Sha2::pad`.
- 2026-11-12: Minus read the two modules and asked what would make them elegant (2026-11-12). A probe first: the generator already takes `u64`/`u8`, numerals, `+ - << >> & |` and `if a < b` in a `runtime fn`, so much of how these modules read is how they were written, not what the language lacks; they are to be respelled. What the language does lack is collected in [[sha256-context-type]], with [[decreases-word-measures-by-hand]], [[bitvec-xor-complement-symbols]] and [[integer-literal-width-suffix]] filed beside it.
