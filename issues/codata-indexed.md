---
title: Indexed codata declarations
status: open
labels: [codata,coinduction,elaborator]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-10-22
---

`codata D : (i: I) -> Type { … }` is refused this round
(`docs/codata-elaborator-design.md` §1). The kernel's `M` is already
indexed: shapes depend on the index, and children's indices are computed by
`next`, with nothing stored. The elaborator's indexed lowerings
(`docs/inductive-indexed-lowering.md`, fording) are inductive-shaped, and
codata needs its own.

Why it matters: strong bisimilarity is an `M` indexed by a pair of trees,
with an `Id` of the labels as the shape. eutt is the same with an inductive
`Peel` in the shape (`docs/kernel-coinduction-design.md` §4). Both are
needed for the library's laws (milestone `it-coinductive`).

Sketch:
- `I` is the index telescope's Σ, as for indexed inductives.
- A constructor's result annotation `C(…) : D(e)` contributes "label `C`
  is available at index `e`". The shape at `i` is the sum of the
  constructors' payloads, with an equation `e = i` stored the way route 1
  stores it (or computed by a case tree on the index, when it is a
  constructor pattern).
- `next(i, s, p)` reads each child's written index off the constructor's
  field type.
- `match` on an indexed codata value refines nothing (no η, so the motive
  stays non-dependent), but the branches see the stored equations.
- Corecursion into an indexed codata type is coinduction proper. The
  carrier is a family `X(i)`, and the self-call's index is checked against
  the child's.
