---
title: Prove log(exp a) ≈ a, and log at real arguments
status: closed
labels: [mathematics,reals]
area: mathematics
milestone: [float-transcendental]
created: 2026-11-01
updated: 2026-11-01
---

`CReal::exp_log_rat(q, pos): exp(log_rat(q, pos)) ≈ ofRat(q)` is proved
for every rational q > 0 (lib/std/analysis/real/real_log.hthr,
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

## Log

- 2026-11-01: Done in lib/std/analysis/real/real_log_law.hthr. `CReal::log(x, h: 0 < x)` reads a lower bound 1/(k+1) from the positivity evidence (`CReal::pos_gap`) and is the `RatLip` extension of log_rat with its argument clamped up to that bound (`Rat::clamp_up`, from abs). The clamped log is (k+1)-Lipschitz on every rational (`CReal::log_rat_sub_le`), from exp(d) >= 1 + d at d >= 0 (`CReal::exp_ge_add_one`) and exp(log q) = q. `CReal::exp_log` is exp(log x) = x at every positive real, from the extension's estimate (`RatLip::ext_dev`) and exp's second-order bound. With injectivity (`CReal::exp_inj`, from `exp_lt`) everything else follows: `log_exp` (log(exp a) = a at every real), `log_mul`, `log_one`, `log_le` (monotone), `log_respects` (the value does not depend on the evidence) and `log_ofRat` (it agrees with log_rat). Not done: strict monotonicity (`x < y → log x < log y` needs a quantitative lower bound on log's increments), and log's derivative 1/x.
