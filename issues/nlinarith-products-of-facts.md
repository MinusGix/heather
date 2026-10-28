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

The `nlinarith` heuristic: before the search, add the pairwise products of the
facts' differences (and the squares of atoms and of differences) as rows, each
proved from its two facts by a monotonicity lemma — `Int::mul_nonneg` and its
strict forms at `Int`/`Nat`, `OrderedField::mul_nonneg` at a field — and let
the existing search (omega, Fourier–Motzkin) find the combination over the
degree-two monomials. This is the first shape of [[ring-inequalities]]
(a sum of nonnegative terms, squares among them) made a search.

## What it assumes from elsewhere

- **[[ring-inequalities]]** (closed): `linarith`'s reading at `Int`/`Nat`, a
  multiplying side stated equal to its monomial form.
- **[[linarith-ordered-fields]]** (closed): the field certificate the product
  rows would join.

## Log
