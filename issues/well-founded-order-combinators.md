---
title: "Well-founded orders as a library: measures, lexicographic products, the multiset order"
status: open
labels: [stdlib,mathematics,order,termination]
area: mathematics
milestone: [math-order-fixpoints]
created: 2026-11-10
updated: 2026-11-10
---

Area 2 of the 2026-11-10 ranking.

`Acc` is defined inside `lib/std/relation/transition.hthr` for the
simulation diagrams. `decreases` clauses rebuild their orders per
function ([[termination-measures]], [[measure-inference]]).

## Scope

- `Acc` and well-foundedness in `lib/std/relation`, with induction and
  recursion principles, moved out of `transition.hthr`.
- Combinators, each with its well-foundedness proved once: inverse image
  along a measure, lexicographic product, sum, the transitive closure,
  and the Dershowitz–Manna multiset order over
  [[finite-maps-and-multisets]].
- `Nat`'s `<` and the structural order of a `Wf` inductive as instances.

## Done when

`transition.hthr` imports `Acc` instead of defining it, and one
`decreases` clause that today spells a lexicographic pair by hand cites
the combinator.

## What it assumes from elsewhere

- **[[termination-measures]]** owns how `decreases` is elaborated.
  Assumed here: only that it can accept a library well-founded relation.
