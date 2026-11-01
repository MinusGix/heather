---
title: Prove exp(log q) ≈ q, and log's laws
status: open
labels: [mathematics,reals]
area: mathematics
milestone: [float-transcendental]
created: 2026-11-01
updated: 2026-11-01
---

`CReal::log_rat` (lib/std/num/float/elementary.hthr) is defined as a sum:
2·atanh(t) after scaling the argument into one binade, plus e·log 2. None
of its laws is proved. [[log-grid-gap]] needs `exp(log q) ≈ q`.

exp is done at real arguments, with its laws
([[elementary-functions-at-reals]], closed): `CReal::exp_add`, monotonicity,
and the Lipschitz bound `CReal::exp_dev` (lib/std/num/float/elementary_real.hthr).
So exp(e·log 2) = 2^e follows from `exp_add`. What is missing is the core
identity

    exp(2·atanh t) ≈ (1 + t)/(1 - t)    for |t| < 1

Scope:

- `exp(log q) ≈ q` for rational q > 0;
- `log(exp a) ≈ a`, which follows from the first because exp is strictly
  increasing (`CReal::exp_lt`);
- log at real arguments, and `log(x·y) ≈ log x + log y`, as consequences.

Routes:

- **Derivatives.** f(t) = exp(2·atanh t)·(1 - t) - (1 + t) has f(0) = 0
  and f' = 0 on (-1, 1). This needs the derivative of a power series inside
  its radius, and a zero derivative implying a constant function
  ([[real-functions-and-derivatives]]).
- **Composition.** exp ∘ (2·atanh) as a power series whose coefficients are
  those of (1+t)/(1-t) = 1 + 2t + 2t² + …, with the composition carried
  through evaluation ([[formal-power-series]], [[power-series-evaluation]]).
  The Cauchy-product machinery in lib/std/num/float/exp_law.hthr
  (`Rat::cauchy_gap`, over term functions) is the analytic half of the
  product step.

## Log

- 2026-11-01: 2026-11-01: Toward the derivative route. In place now: the mean value inequality and `DerivOn::const_of_zero` (real_fn.hthr), exp′ = exp at the reals (`CReal::exp_deriv`, lib/std/analysis/real_exp.hthr), and the product and chain rules. Missing: atanh as a real function on |t| <= r < 1 with derivative 1/(1 - t²), which needs a power series to be differentiable inside its radius, and the bridge from `Series::atanh2(A, B)` to Σ t^(2k+1)/(2k+1) at t = (A - B)/(A + B). The second PR of the thread "Prove the mean value inequality and exp(log q) = q" takes these on.
