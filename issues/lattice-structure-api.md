---
title: Develop lattice structures from orders and indexed operations
status: closed
labels: [stdlib,mathematics,order,algebra]
area: mathematics
milestone: [math-classes]
created: 2026-09-02
updated: 2026-11-02
---

Develop meet/join semilattices, lattices, bounded lattices, and the connection
between their algebraic laws and order universal properties. Both the relation
and operations should be explicit indices, allowing multiple orders or
operations on one carrier.

Begin with the already proved `Nat` and `Int` min/max laws, then add a product
control. Decide from those probes whether order-derived and algebraically
presented lattices are separate interfaces connected by constructors, or one
canonical theory.

## What it assumes from elsewhere

- **[[mathematical-order-hierarchy]]** owns preorder/partial-order structure.
- **[[algebraic-theory-composition]]** owns canonical multi-parent layering.

## Log

- 2026-09-02: Filed as a concrete test of relation-plus-operation theories.
- 2026-11-02: Landed: `lib/std/algebra/lattice.hthr`, design `docs/library/lattice-structure-design.md`. Decided one canonical theory presented by the order: `MeetSemilattice(≈, ≤, ⊓)` / `JoinSemilattice(≈, ≤, ⊔)` / `Lattice` over a new `PartialOrderRel(≈, ≤)` (antisymmetry into `≈`; tagged `Preorder`/`Trans` views as at `StrictOrder`), with the algebraic laws as theorems. The algebraic presentation is `algebra_rel`'s `Mergeable`, reached both ways by constructors (`MeetSemilattice::mergeable`, `Mergeable::meet_semilattice` over `MergeLe(≈, ⊓)`; `le_iff_meet` is the round trip). Bounds are `OrderBot`/`OrderTop` capabilities, with `BoundedLattice` composing them. Instances: `Nat` (`Lattice` at `RelId`, `OrderBot`), `Int` (`Lattice` at `RelId`), `Dyadic` (`Lattice` modulo `Dyadic::Same`); `product_lattice` is the product control. New `⊓` token, multiplicative rung. `Int`'s `Equivalence<Int>(RelId<Int>)` moved from `semiring` to `order`. Probes in `lib/_tests/std/algebra/lattice_tests.hthr` (two lattices on `Nat`, `Bool`'s `&&` order from its algebra). Join is the meet's dual written out; distributive lattices and a generic decidable-order constructor are noted as not done (design §4).
