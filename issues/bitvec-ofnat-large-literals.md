---
title: Make BitVec ofNat conversion scale to full-width machine literals
status: closed
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

## Log

- 2026-09-07: Diagnosed against the current build before changing anything.
  At the reproducer's magnitude the old `ofNat` did not even reach `OutOfFuel`:
  `half` at `2^20` overflowed the checker's native stack, and the x86 byte
  equality at a mere five-digit immediate (70000) exhausted the ordinary
  conversion fuel, so the limit was far tighter than "full-width". The
  two-counter folds the kernel already cancels run against run were fine at
  full width: closed `sub`, `leb`, and `add` on `2^63`-sized literals checked
  in well under a second. What did not was anything that *doubles*:
  `pow(2, 20)` and `twice` overflowed the stack, because the successor-mapping
  fold left its tail pending, so every addition of a run onto a run made one
  more fragment and `pow(2, k)` was a chain of `2^k` single-successor runs.

  Two layers of change. In the library, `ofNat` reads its bits from the
  top: the argument is first reduced below `2^n` by a `decreases`-justified
  repeated subtraction (nothing for a literal within the width, so
  truncation modulo the width is kept for `mul`), then compared against and
  reduced by `[2^(n-1), …, 1]`, built by doubling, consing each bit so the
  last decision — weight one — is the head. `half`/`even_dec` stay as they
  are; they were never the right primitive for this, only the obvious one.

  In the kernel, three small extensions of the run machinery, each found by
  a probe the previous one exposed. (1) The successor algebra is recognized
  at any arity `su^p ih`, scaling a saturated run's count by `p` (`twice`),
  declining to the ordinary step when the count would overflow. (2) The fold
  at the mapped run's tail is forced through a `NatRunTail` frame and a run
  it produces is merged in (`ContextProgram::append`), so `p + p` is one
  saturated run; under conversion's δ-lazy evaluation that tail is usually a
  *glued* definition (`mul(2, k)` unfolded once is `add(mul(2, k-1), 2)`),
  so the frame unfolds glued heads until a run, a constructor, or a stuck
  neutral — keeping the first glued neutral as the tail in the stuck case,
  so an open wrapper is not normalized away. Without this, `mul(2, 65536)`
  overflowed the native stack: conversion recursed once per fragment.
  (3) The two accelerated folds — successor algebra and synchronous
  two-counter — unfold a glued scrutinee (or, for the synchronous fold, a
  glued right-hand counter) themselves instead of stalling as a spine for
  conversion to δ-step from the outside. Each outside δ-step replays the
  whole pending spine, so the doubling chain feeding `le_dec` under `toNat`
  was roughly quartic in the width: the width-64 round trip exhausted fuel
  and the width-56 one exhausted memory, while every pair of the three
  pieces composed cheaply and a *literal* powers list made the whole thing
  cheap. With (3) the round trip is width-linear, and elaborating the x86
  model itself got faster, since its byte constants are the same shape.
  (4) Conversion's same-head case. Two `ofNat(n, k)` at different `k` —
  the shape of every corrupted-encoding control, where a canonical byte
  meets the wrong literal — stop at the same defined head, fail the spine
  comparison, and were then unfolded in lockstep one δ-step at a time with
  everything re-compared each round. A per-conversion count showed why no
  cache could help: 271k sub-comparisons on 271k *distinct* closure pairs,
  because each round re-evaluates the exposed body and every closure
  beneath it is fresh. Conversion now unfolds both sides to their δ-heads
  once the meet at a shared head has failed (a meet at a sub-term is still
  found lazily on the canonical forms' components); the dense width-8 and
  width-64 cases went from `OutOfFuel` to an immediate `NotConvertible`. A
  verdict memo in `Conv::tm` (closure identities, scope, Ψ length, layer;
  never exhaustion) stays for the repeated sub-comparisons a lazy
  comparison does make: the x86 model loads ~30% slower without it.
  Radix spellings (merged from the hex/bin branch) are the same compact
  literal, and a hex-digit-off control at width 64 pins this case.
  A broader rule — unfolding a glued scrutinee for *every* match — was
  tried and rejected: the x86 decoder's open-argument unfolding theorems
  meet at a folded `match decode_opcode_direct(…)`, and eager unfolding
  exhausts fuel on the dispatch that scrutinee hides.
  None of the four guesses a value: (1) is the existing homomorphism rule
  at a wider context, (2) is the representation's own merge rule, (3) is δ,
  confined to the scrutinee of a fold that can only fire on closed
  arithmetic and stops at a variable otherwise, and (4) is a cache of the
  algorithm's own answers.

  Rails: `lib_std_bitvec` checks the asymmetric, high-bit, saturated and
  five-digit literals at width 64 against independently written bit vectors
  and through `toNat`, with single-bit flips and an off-by-one refused as
  `NotConvertible` rather than fuel; `x86_64` pins the little-endian bytes of
  `MovRI` at the asymmetric and high-bit immediates with a big-endian
  control; `function_ir_x86` takes both constants through the reflector,
  lowering and certificate; and the native example now adds the asymmetric
  constant so every exported immediate byte is distinct. Kernel unit tests
  cover the merge, the scaled algebra, and the overflow decline.

  Verification: plain full `scripts/test` on furnace, 2470 passed, 0
  failed, 5 ignored; `scripts/bench --check` on the baseline machine, 106
  comparisons within thresholds (two `check/generated-terms` points
  improved). Residue, owned elsewhere: `half` is still magnitude-linear and
  its stack overflow through `heather check` is logged in
  [[bitvec-closed-reduction-cost]]; closed `mul` at machine width still
  reduces its argument by one width-multiple per step, which is the same
  magnitude-bound as before and not this issue's customer.

