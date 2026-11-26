---
title: Derive every P3109 format's layout from the report's constraints
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

`Format::p3109_layout(K, P, s, d, valid, k1)` (`lib/std/num/float/p3109_codes.hthr`)
takes "the largest finite code is normal" (`2^(P-1) <= top code`) and
`1 <= K` as hypotheses; literal formats close them by evaluation. So the
bijection theorems hold for every format one instantiates, not yet for every
valid one. Prove both from the report's constraints (§3.1: `K >= 3`,
`0 < P < K` signed, `0 < P <= K` unsigned) and add
`Format::p3109_layout_of_valid`, so "for every P3109 format" is one theorem.

The arithmetic: signed, `2^(P-1) <= 2^(K-2) <= 2^(K-1) - 2`; unsigned,
`2^(P-1) <= 2^(K-1) <= 2^K - 3` (for `K >= 3`). Power-of-two monotonicity
(`Nat::pow_le_pow_r`) and `2^(K-1) >= 4`.

## What it assumes from elsewhere

- **[[float-p3109-encoding]]** (closed) owns the layout. Assumed here: only the
  shape of `p3109_layout`'s hypotheses.
