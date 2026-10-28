---
title: Products of facts and squares in linarith (nlinarith)
status: open
labels: [tactics,arith,proofs]
area: tactics
milestone: [tac-arith]
created: 2026-10-28
updated: 2026-10-28
---

`linarith` reads products as monomials at every carrier (docs/linarith-design.md
§3, §8) but combines facts only linearly, so a goal that needs a product of
facts, or a square's sign, is refused: `0 <= x * x`, or `0 <= a * b` from
`0 <= a` and `0 <= b`. The probes hold both as refusals
(`lib/_tests/std/tactic/linarith_tests.hthr`, `int_square_is_not_linear`,
`creal_product_is_not_linear`).

The approach is chosen in docs/nonlinear-arithmetic-design.md: one
certificate (linarith's direct form over product parts, §2), searched first
by the `nlinarith` heuristic, the build this issue owns (§4):

- A tactic `nlinarith(facts…)` separate from `linarith`. Hints are facts
  (`nlinarith(Rat::sq_nonneg(a - b))`).
- Products of every pair of written facts and the negated goal, each fact
  with itself included. Squares are taken from `t * t`, `t.npow(2)` and
  `t ^ 2` seen before normalization, plus every monomial with only even
  exponents. Context facts join linearly and are not multiplied.
- The negated goal is multiplied only where a refutation proves the goal:
  `<=`, `≈`, `¬<` and `False` at every carrier, and `<` at `Rat`/`Int` by
  `lt_of_not_le`. A `<` goal at `CReal` stays direct (§2).
- At `Int`, products go to `omega` as `let` facts with their `ring` bridges.
  At `Nat`, a product is stated additively (`Nat::mul_le_cross`).
- New lemmas: `OrderedField::sq_nonneg` (the constructive proof is sketched
  in §4.5), `Rat::`/`CReal::`/`Int::sq_nonneg`, `Int::mul_nonneg`, the
  `nlin_*` parts in `linarith.hthr`, and the refutation finish.
- `linarith`'s refusal names `nlinarith` when its reading contains a
  nonlinear monomial.

Done when the two probes above are `nlinarith` successes, the refusals in
§4.6 are probes, and at least one hand-written product proof in the library
(`OrderedField::mul_le_mul`, a float error bound in `round.hthr`) is a
`nlinarith` line.

## What it assumes from elsewhere

- **[[ring-inequalities]]** (closed): `linarith`'s reading at `Int`/`Nat`, a
  multiplying side stated equal to its monomial form.
- **[[linarith-ordered-fields]]** (closed): the field certificate the product
  rows would join.
- **[[linarith-positive-denominators]]** (closed): `scale`, which multiplies a
  row's form by a factor's form. Assumed here: only that operation.
- **[[linarith-simplex-search]]** owns the search engine once Fourier–Motzkin's
  row bound refuses a product problem. This round keeps Fourier–Motzkin.

## Log
- 2026-10-28: Design chosen (docs/nonlinear-arithmetic-design.md): one certificate, with nlinarith as the first search. Compared against SOS by SDP (deferred to [[sos-certificate-oracle]], offline and writing hints), polyrith-style oracles (`ring(h)` already searches for equalities), CAD (declined: no certificate, not constructive at `CReal`), and interval branch-and-bound (complementary, [[interval-variable-boxes]]). The body above now records the build.
