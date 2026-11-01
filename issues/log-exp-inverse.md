---
title: Prove log(exp a) ≈ a, and log at real arguments
status: open
labels: [mathematics,reals]
area: mathematics
milestone: [float-transcendental]
created: 2026-11-01
updated: 2026-11-01
---

`CReal::exp_log_rat(q, pos): exp(log_rat(q, pos)) ≈ ofRat(q)` is proved
for every rational q > 0 (lib/std/analysis/real_log.hthr,
[[exp-log-inverse]]). Its converse and the laws that follow are not.

Scope:

- `log(exp a) ≈ a` at rational `a`, as `exp` is strictly increasing
  (`CReal::exp_lt`): if `log(exp a)` were apart from `a`, exp would put
  `exp(log(exp a))` apart from `exp(a)`. This needs `log` at a real
  argument first, since `exp a` is not a rational.
- `log` at a positive real `x`: the binade scaling `log_frac` does at
  rationals has to read `x` through a rational approximation, so the
  natural definition is `CReal::extend` of `log_rat` over a positive lower
  bound, with a Lipschitz bound from `atanh′ = 1/(1 - t²)`
  (`CReal::atanh_deriv`, `DerivOn::lipschitz`).
- `log(x·y) ≈ log x + log y`, from `exp_add` and injectivity of exp.

Note that atanh at the reals is only built on [-1/2, 1/2]
(`CReal::atanh_D`), which is all `Series::atanh2` reaches after binade
scaling (t ≤ 1/3). A wider interval would need the tail bound at r < 1
rather than r = 1/2.
