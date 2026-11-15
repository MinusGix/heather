---
title: Native certificate pieces spend their steps on the encoder's ofNat at closed numerals
status: closed
labels: [kernel,native,bitvec,performance]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-29
updated: 2026-10-30
---

Filed from the packed vector literal round ([[packed-vector-literal-term]], [[kernel-native-bitvector-values]], 2026-10-29). With write-elf's byte literals born packed, what a native certificate piece (`piece_#_is`) still spends is the **encoder's** `BitVec::ofNat` at closed numerals, not the literal side. A per-definition δ-unfold profile of `yes_tool_elf_piece_1_is` (a throwaway patch, debug binary, width one) put the remaining steps on `ofNat`'s own recursion (`cons_bit`, `odd_bit`, `Nat::half`, `from_bits`, a few thousand unfolds each) and `Nat::add` (the `add_nat` address arithmetic). The `ofNat` traffic comes from three places:

- `rr_bytes(opcode: Nat, …)` and its kin (`lib/std/arch/x86_64/x86_64.hthr`) build the opcode byte as `BitVec::ofNat(opcode)` at every instruction;
- `io_data_low().add_nat(n)` addresses: `ofNat(64, …)` of a sum, per address;
- the lowering's immediates, which write-elf still spells `ofNat(64, k)`, because a packed immediate loses the free spine meeting with the lowering's own `ofNat` (packing them made `e_#` about 40 K steps worse and `header_is` about 52 K worse on yes's certificate).

Two levers, not exclusive:

1. **Library**: now that a byte literal costs one evaluator step, pass constant opcode bytes as byte literals (`from_bits(8, [...])`, which the elaborator packs) instead of `ofNat(opcode)`. Unit probe from this round: `canonical_bytes(MovRR …)` went 1,454 → 1,633 steps when only the *expected* side was packed, because the encoder's `ofNat(opcode)` no longer met it at the spine; with both sides packed it should fall well below the original. Measure with `scripts/bench-probes --filter cert/` and a `--only` probe per instruction kind.
2. **Kernel**: `ofNat` at a closed width and a closed numeral reaching a `BitRun` directly. The replay arm (`docs/patches/bitvector-nat-state-arm.patch`, `docs/kernel/bitvector-literal-entry-design.md` §10.7) is correct but was +1.0 % on the reused_callee workload because it replays the step per bit. It has not been measured on the certificate workload, where `ofNat` is a larger share; re-measure it there before building anything new. A constant-time route needs the step's two Nat functions (`odd_bit`, `half`) evaluated as arithmetic rather than replayed, which §10.7 says the probe representation cannot do by substitution.

## Done when

`cert/yes-pieces` is a small fraction of its steps after the packed literal round, or the reason it cannot be is written down.

## Resolution (2026-10-30)

Lever 2, without the replay: the kernel reads `ofNat`'s step as
`cons(f(x), ih(g(x)))` with `f` and `g` chains of classified `Nat` folds,
reads their trees and bases out of the probe as closed data, and at a
closed `x` produces the word by arithmetic (`Output::NatState`,
`Transducer::run_nat`; a functional-graph walk of each window instead of the
tree's powers). No definition is named; library code keeps writing
`ofNat(n, k)`. `docs/kernel/bitvector-literal-entry-design.md` §10.10 has the
adequacy argument and the numbers; `crates/kernel/DESIGN.md` the paragraph.

`cert/yes-pieces` (cloud, interleaved pairs): 488,749 → 327,015 steps,
kernel 0.97 → 0.57 s. `ofNat(64, k)` at a literal: ~2,200 → 268 steps,
flat in the magnitude. What `yes-pieces` still spends is no longer `ofNat`
— the "small fraction" bar is not met by this lever alone; the remainder
(`Nat::add` address arithmetic, the encoders' record and list structure)
is [[native-certificate-pieces-remaining-cost]], and lever 1 (opcode bytes as
literals) is now unnecessary for `ofNat`'s sake. Packing write-elf's
immediates, refused in #269 because the lowering's `ofNat` met them at the
spine, may now be cheap either way and is worth re-measuring.
