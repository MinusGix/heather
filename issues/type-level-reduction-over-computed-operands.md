---
title: A proposition over computed Nat operands costs gigabytes to reduce at the type level where its term-level decision is cheap
status: open
labels: [kernel,elaboration,conversion,performance]
created: 2026-09-09
updated: 2026-09-09
---

Found by the reflection round ([[reflection-through-decide-instances]]),
release checker over the standard library, one probe file per fact, width
64, operands `A = ripple_add(64, ofNat(64, 5), ofNat(64, 2^63 - 5))` and
`B = ripple_add(64, ofNat(64, 2^63), ofNat(64, 1))`:

| fact | route | wall | peak RSS |
|---|---|---|---|
| `or_index(nat::le_dec(toNat(64, A), toNat(64, B))) = 0` | `refl` (term-level) | 4.1 s | 134 MB |
| `unsigned_lt_bit(64, A, B) = True` | `refl` (term-level) | 3.3 s | 129 MB |
| `nat::Lt(toNat(64, A), toNat(64, B))` | `trivial` (type-level whnf) | 14.8 s | 6.5 GB |
| `Decide<nat::Lt(toNat(64, A), toNat(64, B))>` resolved by `nat::Le::Decide` | unification of `Le(?n, ?m)` against the goal | 14.8 s | 6.5 GB |
| any `Decide` candidate whose head differs from the goal's, at these operands | unification, rejected | 14.7 s | 6.5 GB |

Loading the library alone is 3.2 s / 109 MB. The same decision the kernel
performs cheaply as a term — `le_dec` is a synchronous fold, `toNat` over a
ripple sum is the width — costs gigabytes when the elaborator reaches it
through a **type**: the whnf of `Lt(x, y)` that `trivial` reads, or the
conversion that unifies `Le(?n, ?m)` with a goal that unfolds to it. A
rejected candidate pays the same as an accepted one. The constant size of
the cliff (always ~6.5 GB) suggests a budget being exhausted along a path
that retains what it evaluates, not work proportional to the operands.

[[reflection-through-decide-instances]] routes around this — the head-keyed
instance unifies syntactically and is tried first — and does not fix it.
It is the same family as [[kernel-failed-conversion-cost]] (a mismatch
behind shared structure costs a successful proof's budget) with a new
member: a *successful* type-level reduction that the term-level machine does
in a step.

## Acceptance

- The `trivial` row above checks within a small multiple of the library's
  own footprint, or the report says which reduction path the type-level whnf
  takes that the term-level one does not.
- A `Decide` candidate at another head, unified against a goal over these
  operands, is rejected at a cost bounded by the goal's size, not by
  evaluating the operands.

## What it assumes from elsewhere

- **[[kernel-failed-conversion-cost]]** owns the asymmetric failed path in
  general. Assumed here: only that a reduced reproducer belongs there if the
  cause turns out to be the same.
- **[[resolution-candidate-fan-out]]** owns narrowing the candidate set;
  assumed here: only that ordering by head is landed and orthogonal.

## Log

- 2026-09-09: 2026-09-09: A third route into the same cost: the canonical-derivation table's conversion-keyed lookup, comparing Decide<unsigned_lt(64, ofNat(64, 2^63), zero(64))> against Decide<unsigned_lt(64, ripple_add(…), ripple_add(…))> to find them unequal (~6.5 GB, same head). Bounded in [[reflection-through-decide-instances]] by DERIVED_LOOKUP_FUEL; the underlying failed conversion over two closed BitVec values is this issue's.
