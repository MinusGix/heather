---
title: Generate formal covers inductively from axioms
status: open
labels: [stdlib,mathematics,locale-theory,research]
area: mathematics
created: 2026-11-09
updated: 2026-11-09
---

`lib/std/locale/formal_topology.hthr` presents a frame from any cover relation
satisfying reflexivity, transitivity, the `≤`-left rule and localisation
(docs/frame-locale-design.md §6). A particular locale is presented instead by a
small **axiom set**: for each basic open `a: P`, a small type `C(a)` of covers,
each a family `cov(a, k): I(a, k) → P`. Its cover is the least relation closed
under reflexivity, `≤`-left and "infinity" (`k: C(a)` and every
`cov(a, k)(i) ◁ U` give `a ◁ U`), an inductive family with an infinitary
premise (Coquand, Sambin, Smith and Valentini, "Inductively generated formal
topologies").

Build that family, prove transitivity (induction on the first cover), and prove
localisation under the localisation condition on the axioms (for `b ≤ a` and
`k: C(a)` there is `k': C(b)` whose members are each below `b` and below some
member of `cov(a, k)`), which takes a double induction. The result is a
`FormalTopology`, so `FormalTopology::frame` gives its frame unchanged.

Customers: `localic-real-numbers` (rational intervals with the interval-
splitting and shrinking axioms), the localic product, and spectra of rings.

Also here: the Heyting implication of a presented frame. `x ⇒ y` is a join
indexed by elements, which a large carrier cannot index, but in a presented
frame it is the join over basic opens `a` with `↓a ⊓ x ≤ y`, a small index.

## What it assumes from elsewhere

- **[[frame-and-locale-foundations]]** owns the frame classes, `FormalTopology`
  and its frame. Assumed here: only that an axiomatic cover presents a frame.
- **[[indexed-infinitary-families]]** (premises quantifying over an argument)
  owns the family shape the inductive cover needs; assumed only that such a
  family lowers and supports recursion over the premise.

## Log

- 2026-11-09: Filed from frame-and-locale-foundations, whose presentation
  basis is axiomatic.
