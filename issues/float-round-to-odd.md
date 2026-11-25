---
title: Round-to-odd, and its exactness check under saturation
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [p3109-projection]
created: 2026-11-25
updated: 2026-11-25
---

Design §5.4 plans round-to-odd "as an internal mode for double-rounding
proofs when a round needs it". P3109 makes it a user-facing mode
([[float-p3109]]). Add it: the result is the input when representable,
otherwise the neighbour with an odd significand (at precision one, read
"odd" the way [[float-precision-one]] reads "even").

## The caveat FLoPS found (§3.3)

Round-to-odd's selling point is that an even result certifies the
rounding was exact, which is what makes it safe for double rounding. That
holds for every value inside the finite range. Under saturation it holds
only if the saturated value has an odd significand, and that depends on the
format: the largest finite value is odd in a signed finite P3109 format, but
even where the top significand is reserved (unsigned finite, signed
extended at `P > 1`, and the library's own E4M3, whose NaN takes the top
code). So the theorem is:

- `even(○ₒ(x)) → ○ₒ(x) = x` for `x` in the finite range, at every format;
- outside it, only for formats whose extreme finite significand is odd,
  with a negative control at E4M3 (a saturated input with an even result
  that is not exact).

## Then

The double-rounding theorem: rounding to odd at `p + 2` bits and then to
nearest at `p` bits equals rounding to nearest at `p`, which is the use
design §5.4 had in mind.

## What it assumes from elsewhere

- **[[float-saturation-modes]]** owns saturation as a parameter. Assumed
  here: only that a projection can saturate in a format with infinities.

## Log

- 2026-11-25: Partly landed (design §6): `Format::round_odd` (truncate, step away when inexact on an even code; a function beside `Mode`, not a constructor) and `round_odd_faithful`; tests pin both parities, precision one, and the saturation caveat (E4M3 gives its even largest float 448 for 460). Still open: "even implies exact" inside the range (needs the step's parity from `UpIs` at the half-unit level), the double-rounding theorem, and round-to-odd through `project`'s saturation modes.
