---
title: bv_omega overflows the stack on word_of_nat at an open value
status: closed
labels: [bitvec,omega,crash,metaprogramming]
created: 2026-09-27
updated: 2026-09-27
---

`bv_omega` crashes the process (a Rust stack overflow, not a refusal) on a
goal that mentions `word_of_nat` at an open value:

```text
import bitvec; import bitvec_nat; import bitvec_omega; import nat; import logic; import omega;

theorem self_sub(e: Nat): bitvec_nat::word_of_nat(64, e).sub(bitvec_nat::word_of_nat(64, e)).toNat() = 0 { bv_omega }
-- thread 'main' has overflowed its stack
```

The same goal over a variable word (`a.sub(a).toNat() = 0`) checks.
`word_of_nat(n, v)` is `BitVec::zero().iterate_increment(v)`. The guess to
verify first is that `bv_omega`'s definition walk (docs/tactics/bv-omega-design.md §2,
"a definition") steps into `iterate_increment`, a recursion on an open count,
and never reaches a leaf. A recursive definition should be a leaf, or at least
bounded. Found 2026-09-27 while probing [[linux-syscall-trace-model]]'s failure
paths. `errno_word` was changed to `BitVec::ofNat`, which also evaluates in
width-bounded steps, so that round no longer meets it.

## Acceptance

- The reproducer is refused with a message or proved; no crash.
- A test pins it, beside `bv_omega.rs`'s existing negatives.

## Log

2026-09-27: Fixed the bound planner's dependency cycle. The definition walk
already recognizes `word_of_nat`; the crash occurred while emitting its
bound. In `w.sub(w)`, the shared operand's bound was taken from the
subtraction's minuend, which is that same operand. Nested shared operands
can close a longer cycle through an addition's bound. The planner now
rejects any parent edge whose bound dependency reaches the operand and
uses an independent stated bound or side condition instead.

The reproducer is refused with `does not fit 64 bits`. Regression tests
cover bounded self subtraction, nested sharing with and without a bound,
variable-word self subtraction, and a false equality control.
