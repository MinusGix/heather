---
title: CReal::compress, correct rounding of reals, and correctly rounded exp and log
status: closed
labels: [stdlib,mathematics,reals,float]
area: mathematics
milestone: [float-reals, float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

With `CReal` on dyadic terms at the binary rate
([[creal-dyadic-binary-rate]]), the 60+ bits that correctly rounded `exp` and
`log` need are an index, not a term 2^60 out. This round starts the two
submilestones that were waiting on it:

- `CReal::compress` (O'Connor's): read one index further out and floor to
  n+1 bits, proved `≈ x`. The operations already round, except sums,
  negations, limits and hand-built reals; this is the opt-in for those.
- `float-reals`' core: `RoundsToReal(F, mode, x, r)`, a rational interval
  around `x` that rounds to `r` throughout, equal to `RoundsTo` at an
  embedded rational, unique up to `Float::Same`, and Ziv's search over any
  `Enclosed` real that returns a float only with that proof.
- `float-transcendental`'s start: `Format::exp_fin` and `Format::log_fin` at
  finite floats, with `CReal::log_rat` (atanh after scaling into one binade)
  new beside `exp_rat`.

Design and results: docs/library/creal.md.

## Log

- 2026-10-31: landed. binary32 exp and log compute by evaluation in the
  kernel's step budget for moderate arguments; binary64 and larger
  arguments do not yet ([[interval-evaluation-budget]]). Termination of the
  search is [[float-round-real-termination]]; the IEEE special cases are
  [[float-exp-log-specials]]; log's law against exp stays with
  [[elementary-functions-at-reals]].
