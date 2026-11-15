---
title: Interval enclosures over Dyadic and a reflective inequality tactic
status: closed
labels: [mathematics,tactics,reals]
area: mathematics
created: 2026-10-25
updated: 2026-10-26
---

CoqInterval proves inequalities about real expressions, integrals included,
by evaluating enclosures (`docs/surveys/coq-hardware-floats-survey.md` §6.1). Its
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

## Log

- 2026-10-26: LANDED: `lib/std/num/float/interval.hthr` (design
  `docs/library/floating-point-design.md` §16). Intervals of two dyadics or `Whole`,
  containment at `Rat` with the vacuous reading of crossed bounds; `neg`,
  `add`, `sub`, `mul`, `recip` (to `Whole` around zero), constants and powers
  by squaring, each with its containment theorem; rounding at `p` bits is a
  shift on `Dyadic` itself (`Dyadic::down`/`up`), not `Format::round_dyadic`,
  since an enclosure wants no exponent bound and no overflow. The checker is
  `IntervalExpr` with `lt_search`/`le_search` doubling the precision on a miss and
  `lt_of_search`/`le_of_search` turning the verdict into the inequality;
  `Rat::npow(1 + Rat(1, 1000), 1000) < Rat(2719, 1000)` is proved at 32
  bits. `Dyadic::le_dec` now compares aligned mantissas.

  `by intervals()` (`lib/std/tactic/interval_tactic.hthr`) reads the goal
  into the trees, so clients never write them.

  Residue, each with an owner: containment at `CReal` and decided `CReal`
  comparisons are [[interval-creal-enclosures]] (the ordered-field statement
  waits on `float-reals`); `exp`/`log`/`sin` by series are
  [[interval-elementary-functions]].
