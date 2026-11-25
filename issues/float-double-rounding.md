---
title: Double rounding through round to odd
status: open
labels: [mathematics,floating-point]
area: mathematics
milestone: [math-float]
created: 2026-11-25
updated: 2026-11-25
---

Rounding to odd at `p + 2` bits and then to nearest at `p` bits equals
rounding to nearest at `p` (Boldo and Melquiond's double-rounding theorem):
the use design §5.4 of `docs/library/floating-point-design.md` had in mind for
round to odd, and the reason P3109 offers `ToOdd`.

## What it assumes from elsewhere

- **`lib/std/num/float/project.hthr`** owns `Format::round_odd` and its
  exactness (`round_odd_even_exact`, docs/library/float-p3109-design.md §6).
  Assumed here: only that an even result inside the range is exact.

## Notes

The two formats are a narrow `F` and a wide `G` with two more fraction
bits and a range that contains `F`'s. The proof is usually stated as: the
odd rounding lands on a midpoint of `F` only when the value is that
midpoint, because a midpoint of `F` is an even float of `G` and
`round_odd_even_exact` makes it exact. Conversion from `G` to `F` is
`Format::round_dyadic` of the `G` float's dyadic.
