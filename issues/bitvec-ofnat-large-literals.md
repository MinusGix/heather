---
title: Make BitVec ofNat conversion scale to full-width machine literals
status: open
labels: [stdlib,bitvec,performance,x86]
created: 2026-09-07
updated: 2026-09-07
---



## Reproducer

In the normal x86 proof-library context, check a reflexivity theorem equating
`canonical_bytes(MovRI(R9, bitvec::ofNat(64, 81985529216486895)))`
with its literal little-endian byte list. This exhausts kernel fuel even for
one instruction. This was isolated from the new native encoder test, after
splitting the original ten-instruction byte equality into individual checks.
A small immediate such as 7 works in the full source-to-native example.

`bitvec::ofNat` computes bits through `nat_bit` / `nat::even_dec` and
`nat::half`; the latter two recurse by subtracting two from the input Nat.
Investigate a certified route whose cost depends on bit width rather than
literal magnitude. Preserve logical semantics and ordinary kernel rejection
of false conversion claims; do not merely increase fuel or trust the encoder.

## Acceptance

- Full-width asymmetric and high-bit u64 literals check through the source
  reflector, x86 certificate, and exported-byte equality of [[x86-native-export]].
- Little-endian bytes are checked for a multi-byte asymmetric constant.
- Cost is bounded by width, with explicit negative conversion controls.

This issue owns literal conversion performance; [[function-ir-x86-proof-scaling]]
owns scaling with graph size.
