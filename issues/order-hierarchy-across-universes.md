---
title: "One order hierarchy for carriers at Type and at Type<1>"
status: open
labels: [stdlib,mathematics,order,design,classes]
area: mathematics
milestone: [math-order-fixpoints,math-classes]
created: 2026-11-10
updated: 2026-11-10
---

Minus, 2026-11-10: "We should unify the order hierarchy ideally, may need
language bits but that's fine."

`lib/std/locale/frame.hthr` declares `Preorder1`, `FiniteMeets` and
`SupLattice` over `A: Type<1>` because opens are predicates and live one
universe up. `lib/std/algebra/order.hthr` and `lattice.hthr` declare
`Preorder`, `PartialOrderRel`, `MeetSemilattice` and the rest over
`A: Type`. A theorem about meets is proved twice, and a Galois connection
between a frame and a small lattice has no class to be stated against.

## To decide (design, for Minus to review)

- The language route: classes polymorphic in the carrier's universe
  (`class Preorder<A: Type<u>>`), which needs universe-polymorphic class
  declarations, instance resolution at a level, and section opening
  across levels. File the language issues this finds; do not work around
  them in the library.
- The presentation mismatch: `frame.hthr` is presented by `≤` alone,
  `lattice.hthr` by `(≈, ≤)` with antisymmetry into `≈`
  (`docs/library/lattice-structure-design.md`). Decide which the unified classes
  take, and whether frames gain `≈` as the symmetric part of `≤`.
- Whether set-indexed joins (`sup: (I: Type) → (I → A) → A`) sit above
  `JoinSemilattice` in the one hierarchy.

## Done when

A design note settles the three points, and `frame.hthr` extends the
classes of `order.hthr`/`lattice.hthr` with no `Preorder1`.

This is a class-hierarchy shape: the PR that builds it is Minus's to
merge.
