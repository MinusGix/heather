---
title: Real functions, Lipschitz bounds and a constructive derivative
status: open
labels: [stdlib,mathematics,constructive]
area: mathematics
milestone: [math-reals, ml-descent]
created: 2026-10-21
updated: 2026-11-01
---

Functions on `CReal` with a modulus of continuity, Lipschitz bounds, and a
constructive derivative (Bishop-style uniform differentiability is the
obvious candidate; compare a derivative on an abstract ordered field), with
the chain rule and derivatives of polynomials. Then `exp`, `log`, `tanh`
and `sqrt` as real functions with their laws and derivatives.

Customers: ML smoothness and descent (`docs/wick-survey.md` §4.1, §3.5),
activation functions, the float library's transcendental specifications. A
formal derivative on polynomials is enough for the first ML round, so this
can proceed at its own pace.

## What it assumes from elsewhere

- **[[real-completeness-interfaces]]** owns completeness. Assumed here: only
  that limits of regular sequences are available where the elementary
  functions need them.

## Log

- 2026-10-27: docs/analysis-foundations-design.md §7.2 proposes Bishop's uniform derivative stated as a uniform first-order expansion ([[certified-expansions]]), with the rules from jet identities ([[formal-power-series]]) plus remainder lemmas ([[asymptotic-relations]]), and the mean value inequality by telescoping. The derivative is the `C¹` instance of the differential-structure interface ([[differential-structures]], §3.1); Lipschitz functions with the Edalat–Lieutier interval derivative are its lax instance.
- 2026-10-31: First round: `lib/std/analysis/real_fn.hthr`. It is stated once over `K: OrderedField` and read at `Rat` and `CReal` in `lib/_tests/std/analysis/real_fn_tests.hthr`. Predicates: `BoundedOn`, `LipschitzOn` (it quantifies over the bound `h` with `|y - x| <= h`, so no `abs` is needed), `UnifContOn`, `MapsTo`, and Bishop's uniform `DerivOn(D, f, g)`. Moduli are data, and "a positive below both" comes from cotransitivity (`OrderedField::below_both`), with no `min`. Rules: const, id, add, scale, product, chain, finite sums, powers (`npow` with `npow_deriv`, so the exponent never truncates) and polynomials. A bounded derivative gives a local Lipschitz bound `M + 1` at the modulus scale. The product and chain rules take bounds on the factors and derivatives as hypotheses. The refutation `¬ DerivOn(id, 0)` keeps the definition from being vacuous. Left for later rounds: the mean value inequality ([[mean-value-inequality]]); `exp`, `log`, `tanh` and `sqrt` as real functions (`exp` meets [[elementary-functions-at-reals]], whose `CReal::extend` from a Rat-Lipschitz function is the bridge to `LipschitzOn` at `K = CReal`); the Edalat–Lieutier lax instance; and the [[differential-structures]] interface over `DerivOn`. Found along the way: [[ring-atom-mentions-class-constant]] and [[nested-exists-match-cost]].
- 2026-11-01: 2026-11-01: The mean value inequality is done ([[mean-value-inequality]]): `DerivOn::mvi`, `DerivOn::lipschitz` and `DerivOn::const_of_zero`. exp′ = exp at the reals is lib/std/analysis/real_exp.hthr (`CReal::exp_deriv` on any domain where exp is bounded, `exp_deriv_within` and `exp_lipschitz_within` on intervals), from the second-order bound `CReal::exp_sub_lin`: |exp(h) - 1 - h| <= C·k² for |h| <= k <= 1/2. Still open here: log, tanh and sqrt as real functions; uniqueness of the derivative; and the derivative of a power series inside its radius, which atanh needs for [[exp-log-inverse]].
- 2026-11-01: atanh is a real function on [-1/2, 1/2] with derivative 1/(1 - t²) (`CReal::atanh_deriv`, lib/std/analysis/real_log.hthr), from two new rules in lib/std/analysis/real_fn_limit.hthr: the uniform-limit rule `DerivOn::of_approx` (a uniform limit of functions whose derivatives converge uniformly to a uniformly continuous g has derivative g), which is how a power series is differentiated inside its radius, and the reciprocal rule `DerivOn::recip` (taking the inverse as a function with v·u ≈ 1, so nothing is decided). `DerivOn::restrict` narrows a domain. Still open: tanh and sqrt as real functions, uniqueness of the derivative, and log at real arguments ([[log-exp-inverse]]).
