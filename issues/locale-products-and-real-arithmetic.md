---
title: Present the product of locales, and addition and multiplication of the line as maps
status: open
labels: [stdlib,mathematics,reals,locale-theory]
area: mathematics
created: 2026-11-10
updated: 2026-11-10
---

The product of two presented locales is presented on pairs of basic opens,
with each factor's axioms applied in one coordinate
(docs/library/frame-locale-design.md §7 lists it as not done). With it, addition and
multiplication of the real line are maps of locales `R × R → R`, given on
generators and checked on `RealAxiom`'s two constructors through `Cover::hom`
(lib/std/locale/presentation.hthr), as `RealLine::negation` is.

## Scope

- `Cover` for the product axiom set, its localisation, the two projections as
  `LocaleMap`s and the pairing of two maps, each by `Cover::hom`.
- Addition: the inverse image of `(p, q)` is the join of the boxes
  `(a, b) × (c, d)` with `p <= a + c` and `b + d <= q`. Its `Shrink` and
  `Split` cases need fine covers (see [[localic-real-points-are-cauchy]] step 1).
- Agreement with `CReal`'s operations on points, as `CReal::neg_point` states
  for negation.
- Multiplication after addition; it is where interval arithmetic's sign cases
  enter, so consider taking the generator data from the float library's
  interval product and its containment theorem (docs/library/localic-reals-design.md §7).

## What it assumes from elsewhere

- **[[localic-real-numbers]]** owns the line's presentation.
