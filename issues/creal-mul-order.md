---
title: Relate products of regular Cauchy reals to the order
status: closed
labels: [stdlib,mathematics,reals,order]
created: 2026-10-17
updated: 2026-10-18
---

Relate the product of regular Cauchy reals (`lib/std/num/creal.hthr`) to the
order: `mul_pos` (0 < x and 0 < y give 0 < x * y), `mul_nonneg`, and
`mul_le_mono_r` for a nonnegative factor.

Unlike a sum, a product's gap is not termwise. x * y reads its factors at
an index set by their canonical bounds, and a positive gap of the product
needs each factor bounded *below* past its own gap's start. The plan: read
both factors past the later start, where each term is at least 1/(k+1),
so their product is at least 1/((k+1)(l+1)), then use `lt_of_term`.

## What it assumes from elsewhere

- **[[creal-multiplication]]** owns the product and `mul_close`.
- **[[creal-order-and-bishop-bridge]]** gave `≤` with addition
  (`add_lt_mono`, `add_le_mono`, `add_lt_cancel`), which the
  non-strict forms can reuse through x * z - y * z ≈ (x - y) * z.

## Log

- 2026-10-18: Done in docs/creal-mul-order-round.md: `mul_pos` is termwise (a product reads both factors at one index past both starts, gap = product of gaps via `Rat::inv_succ_mul`; no `lt_of_term`), `mul_nonneg` refutes a gap below zero through Bishop's form and `Rat::mul_nonneg_approx`, and `mul_le_mono_r/l`, `mul_lt_mono_r/l` are those signs on the difference. Sign of the inverse has no issue yet; file it when a client needs it.
