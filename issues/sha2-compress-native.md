---
title: SHA-2's compression function as a certified runtime fn
status: open
labels: [cryptography,native,x86,compiler]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-10
---

Stage C1 of `docs/native-lexer-crypto-roadmap.md` §4: SHA-2's compression
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
