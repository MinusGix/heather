---
title: Interval enclosures over Dyadic and a reflective inequality tactic
status: open
labels: [mathematics,tactics,reals]
area: mathematics
created: 2026-10-25
updated: 2026-10-25
---

CoqInterval proves inequalities about real expressions, integrals included,
by evaluating enclosures (`docs/coq-hardware-floats-survey.md` §6.1). Its
original arithmetic matches Heather's `Dyadic` exactly: an integer mantissa
and exponent, an unbounded exponent, no infinities, and every operation at a
requested precision with exact directed rounding. Heather has the pieces
already. `Dyadic` has its ring and order (`lib/std/num/float/dyadic.hthr`),
and `Format::round_dyadic` rounds toward `-∞` and `+∞` exactly at any
`Format`, so a format with a wide exponent span is a precision knob.

## Sketch

- `Interval` of two dyadics, with containment `lo <= x <= hi` stated at any
  ordered field (at `Rat`, and at `CReal` once `float-reals` transfers).
- Operations at precision `p`: `+`, `-`, `*`, division by an interval
  apart from zero, each rounding its bounds outward, each with a containment
  theorem. Elementary functions (`exp`, `log`, `sin`) by series with
  remainder bounds come later.
- **A total interpretation.** As in CoqInterval, an ill-formed interval
  denotes the empty set, so every containment theorem holds vacuously on it.
  That needs no well-formedness field and no runtime test. Heather usually
  carries evidence; for a reflective checker the verdict is the only thing
  proved, and the vacuous reading is cheaper.
- A reflective tactic: reify a real expression, evaluate its enclosure at a
  starting precision, and refine the precision on failure. Evaluation cost
  scales with the bits carried, so start low. CoqInterval's 30-bit default
  proved 87 of its 101 benchmark goals.

## Customers

- `float-transcendental`: Ziv's loop is refinement of an enclosure until it
  misses every rounding breakpoint (design §6).
- Deciding `CReal` comparisons at concrete arguments by evaluation.
- Error bounds in the ML milestones.

No customer is pulling yet, so there is no milestone. This issue records the
design so that whichever of the customers above arrives first starts from it.
