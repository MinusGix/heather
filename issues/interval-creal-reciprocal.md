---
title: Reciprocals in the CReal interval checker, apartness by enclosure
status: closed
labels: [reals,intervals]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

`RealExpr` (`lib/std/num/float/creal_interval.hthr`) has no reciprocal:
`CReal::inv` takes a proof that its argument is apart from zero, and an
expression tree does not carry one, so `by intervals()` reads `x⁻¹` as a
leaf enclosed from its terms (`docs/library/floating-point-design.md` §16,
"Enclosures of reals").

The enclosure can supply the proof. An enclosure of `a` that lies above
zero (`Interval::below(point(0), I)`) gives `0 < a.eval()` by
`Interval::lt_of_below_real`, which is `Apart(0)`; so an `RInv(a, h)` node
whose `h` the tactic builds from a search on `a` alone, and whose
containment is `recip_has` read at `CReal` (the rational proof's
`recip_le_recip` with `CReal`'s inverse order facts, `docs/library/creal.md`).

Scope:

- `Interval::recip_has_real` for an interval that excludes zero, with the
  `CReal` order facts for inverses it needs in `creal.hthr`;
- an `RInv` node carrying the apartness proof, its `eval` spelled as
  `CReal::inv` so the goal converts;
- the tactic reading `CReal::inv` and proving the apartness by its own
  search before the outer one.

## What it assumes from elsewhere
- **[[interval-creal-enclosures]]** (closed) owns `RealExpr` and
  `Interval::HasReal`.
- **[[regular-cauchy-reals]]** owns `CReal::inv` and its laws.

## Log

- 2026-10-27: LANDED (design `docs/library/floating-point-design.md` §16,
  "Reciprocals of reals"). `RInv(a, x, h)` carries the real it inverts and
  the proof, beside the tree that encloses it; `RealExpr::Wf` asks that
  `a` denote `x` (reflexivity for a tree read off a goal, `wf_plain` for one
  with no inverse), and the search theorems take the two sides' witnesses.
  `Interval::recip_has_real` at `CReal` through `CReal::inv_le_inv` and
  `CReal::inv_neg` (`creal.hthr`). `Interval::apart_of_excludes` and
  `RealExpr::apart_of_search` prove apartness by enclosure; `by
  intervals()` reads `CReal::inv` and proves `x.Apart(y)` goals, so
  `x.inv(h := by intervals())` works. The issue's sketch of the node,
  `RInv(a, h: a.eval().Apart(0))`, is inductive-recursive; the named real
  and the witness replace it.
