---
title: Prove the structural carry bit agrees with the arithmetic carry proposition
status: closed
labels: [stdlib,mathematics,proofs,x86]
created: 2026-08-26
updated: 2026-08-26
---

`lib/std/bitvec.hthr` now has two deliberately different views of addition
carry. `carry_add(n,a,b)` is the reusable arithmetic proposition stated through
unsigned interpretation. `carry_add_bit(n,a,b)` is the structural ripple-carry
Boolean needed by executable instruction semantics: deciding the former at an
open width caused the first x86 `ADD` spike to normalize comparisons involving
`2^64` and exhaust the 4 GiB test-process limit.

Prove their correspondence without making either definition an x86 concern.
The useful public shapes are both directions between
`carry_add_bit(n,a,b) = True` and `carry_add(n,a,b)`, plus the false/refutation
side if a customer demands it. Keep the proof open in the width and operands;
closed 4- and 64-bit examples are controls, not acceptance.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns the carrier, arithmetic interpretation,
  and both carry views. This issue owns only the correspondence proof exposed
  by their first executable machine customer.

## Log

- 2026-08-26: Filed from the `ADD r64,r64` semantic spike. The structural view
  made flag computation linear in the width and closed 4-bit controls compute;
  the theorem relating it to the already-landed arithmetic proposition remains.
- 2026-08-26: LANDED and closing. `std/nat` now exposes structural `twice`, its
  exact relationship to self-addition and addition, a middle-sum permutation,
  and the two order reflections `2n <= 2m` / `2n <= 2m+1` iff `n <= m`.
  `BitVec::toNat` uses that structural double in place of open unary
  multiplication; its numeric meaning is unchanged, while one binary digit is
  now one visible proof step. The carry proof generalizes over an incoming bit,
  normalizes each value into low-bit plus twice-tail form, checks the eight
  full-adder cases through the two order lemmas, and inducts on the open width.
  Public `carry_add_bit_true_iff`, `carry_add_of_bit_true`, and
  `carry_add_bit_of_carry` connect the executable bit to the original unsigned
  inequality. Tests apply both directions at open operands and specialize the
  arithmetic-to-bit direction at width 64 under the ordinary rails; no
  `2^64` numeral is normalized.
- 2026-08-26: Post-close resource diagnosis clarified what the correspondence
  buys and what it does not. It avoids the inherently enormous closed unary
  arithmetic decision, but forcing the supposedly linear structural function
  over generated closed vectors still crashes below width 64. That independent
  value-domain/evaluator defect is [[bitvec-closed-reduction-cost]]; automating
  the induction and eight finite cases is
  [[certifying-arithmetic-proof-automation]].
- 2026-08-26: The inner eight-case `carry_threshold` proof is now reconstructed
  by the checking-only `arith` form. The public theorem and outer width
  induction are unchanged; this is a proof-source simplification whose emitted
  match and structural-order certificates still pass the ordinary kernel gate.
