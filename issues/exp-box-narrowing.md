---
title: Prove exp's series boxes narrow, so the Option search over them ends
status: open
labels: [mathematics,reals,float]
area: mathematics
milestone: [float-transcendental]
created: 2026-10-31
updated: 2026-10-31
---

`Float::exp_total` (lib/std/num/float/transcendental.hthr) rounds exp with
no `Option`. It searches over `CReal::enclosed(exp_rat(x))`, the real's own
boxes `x.seq(n) ± 2^-n`, because those have a narrowing proof
(`CReal::enclosed_narrows`). `Float::exp` and the probes' `refl` values
search over the series boxes `CReal::exp_box` (`Series::enclose_auto`),
and nothing proves those narrow. So the gap alone does not show that
`Float::exp`'s `None` never happens with enough tries.

Scope:

- `Series::enclose_auto(p)` is narrower than `2^-k` once `p` is past some
  bound in `k`. Through `Enclosed::narrows_of`, that gives
  `CReal::exp_box(a).Narrows(n, p, 16)`. The box is `settle`'s result. Its
  width is the term box's tail plus the sum box's own width, and both shrink
  with the precision `p` and the term count. This is interval width theory
  that `interval.hthr` does not have yet: the width of `add`, `mul` and
  `Dyadic::down`/`up` at precision `p`.
- Then `Format::exp_fin_ends`: some try count makes `exp_fin` return
  `Some`, by `round_real_ends` with `exp_off_grid`. A total exp over the
  cheaper boxes could then replace the `CReal::enclosed` one.
- Measure what evaluating `Float::exp_total` by `refl` costs. Its try count
  is computed through the proofs (the Padé index for the format's `d`, the
  Archimedean bound on the distance), and nothing has run it.

## What it assumes from elsewhere
- **[[exp-log-grid-gap]]** (closed) gives the gap: `Format::exp_off_grid`.
