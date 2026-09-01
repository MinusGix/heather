---
title: Prove commutativity and foundational algebra for BitVec addition
status: open
labels: [stdlib,bitvec,proofs,arithmetic,compiler]
created: 2026-09-01
updated: 2026-09-01
---

`bitvec::add` is mathematically commutative, but the current library exposes no
checked theorem stating that fact. Its implementation is deliberately simple
and asymmetric:

```
iterate_increment(n, left, toNat(n, right))
```

Consequently commutativity is not a small definitional proof like the
pointwise AND/OR/XOR laws. A useful proof likely wants a reusable arithmetic
characterization of `toNat(add(...))` modulo `2^n`, or a more symmetric
ripple-add definition plus a theorem connecting it to the existing semantics.
Do not make the x86 selector trust a host-side `is_commutative` flag in place
of this law.

This is compiler-motivated but belongs in the generic BitVec library. Besides
enabling right-operand reuse for x86 destructive Add, the resulting laws should
support optimization proofs such as reassociation and constant folding.

## Acceptance

- A checked `bitvec::add_comm(n, left, right)` theorem works at open width and
  for open operands.
- The route preserves the existing wrapped-add semantics and
  `add_sub_cancel`; changing representation requires an explicit equivalence
  proof rather than silently changing the public operation.
- Supporting `toNat`/modular or ripple-add lemmas are stated generically enough
  to reuse in later arithmetic optimization proofs.
- Focused controls cover width zero, width one, machine width, carry-out, and
  unequal high-bit operands.
- [[function-ir-x86-commutative-reuse]] consumes the checked theorem and then
  enables reversed Add selection without trusting the compiler.

## What it assumes from elsewhere

- **[[fixed-width-bitvectors]]** owns the BitVec semantic surface.
