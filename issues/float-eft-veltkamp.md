---
title: Veltkamp splitting
status: open
labels: [mathematics, floating-point]
area: mathematics
milestone: [float-eft, math-float]
created: 2026-10-31
updated: 2026-10-31
---

Veltkamp's split of a float `x` with `C = 2^s + 1`: `γ = ○(C·x)`,
`δ = ○(x - γ)`, `xh = ○(γ + δ)`, `xl = ○(x - xh)` gives `x = xh + xl` with
`xh` on `prec - s` bits and `xl` on `s` bits, in a nearest mode without
overflow of `C·x` (design §19). It is what Dekker's product needs where
there is no fma.

## What it assumes from elsewhere

- **[[float-eft-sterbenz-fast2sum]]** owns Sterbenz and the addition error.
  Assumed here: `δ`, `xh` and `xl` reduce to them.

## Notes

The bit-width conclusions need a predicate "representable on `k` bits"
(`m·2^e` with `|m| < 2^k`), which the module does not have yet; it is the
`rep_below` statement with `top` replaced by `2^k`. Boldo's proof (2006)
also covers the nearest-away tie rule, which the textbook proof omits.
