---
title: Certify one perturbation expansion end to end through the full layers
status: blocked
labels: [mathematics,analysis]
area: mathematics
milestone: [math-reals]
blocked-by: [finite-difference-calculus, formal-power-series, asymptotic-relations, valued-rings-and-newton, certified-expansions, taylor-model-enclosures, regular-perturbation-expansions]
created: 2026-10-27
updated: 2026-11-01
---

The acceptance test that runs through every layer of
`docs/analysis-foundations-design.md` (§13, item 0). Each layer is built in
its proper, general form in its own issue, never as the minimum this one
result needs; this result is checked at each layer as it lands, and is
closed by the general theorem of the last one.

The result is the worked example of §10.1: `x² + εx − 1 = 0` near `x₀ = 1`
has a root `x(ε) = 1 − ε/2 + ε²/8 + R` with `|R| ≤ C·|ε|⁴` for `|ε| ≤ r`,
with `C` and `r` rationals given as data.

Order, each step closing its layer issue in full:

1. **A′** ([[finite-difference-calculus]]). Binomial coefficients and
   Pascal's rule, the binomial theorem, Vandermonde, telescoping, summation
   by parts, the geometric sum. Check here: the residual
   `F(x₂, ε) ≈ ε⁴/64` by `ring` at `CReal` (denominators cleared:
   `y·y + 8·ε·y − 64 ≈ ε⁴` for `y = 8 − 4ε + ε²`).
2. **B** ([[formal-power-series]]). Hurwitz series and jets with the whole
   of their scope. Check here: Newton on jets in `ε` finds
   `1 − ε/2 + ε²/8` from `1`, and the residual's jet vanishes below `ε⁴`.
3. **C** ([[asymptotic-relations]]). Approaches and the Landau relations on
   germs, which the archimedean dominance instance needs.
4. **Axis 2** ([[valued-rings-and-newton]]). The dominance interface with
   both instances, convergence with rates, the fixed-point theorem in a
   complete structure, Hensel and Kantorovich. Check here: the chord map
   `T(x) = x − F(x, ε)/2` satisfies `T(x) − T(y) = (x − y)(1 − (x + y + ε)/2)`,
   with factor `−ε²/8` at `x₂`, so it contracts at rate `< 1/2` on the ball
   of radius `ε⁴/64` around `x₂` for `|ε| ≤ 1/2`; the root exists with
   `C = 1/64`, `r = 1/2`.
5. **D** ([[certified-expansions]]). The record and its algebra. The
   function is given on the neighbourhood, not totally, so a root that
   exists only for `|ε| ≤ r` needs no clamping. Check here: the record
   instantiated at the root.
6. **Uniform bounds** ([[taylor-model-enclosures]]), then **F**
   ([[regular-perturbation-expansions]]): the general theorem, an invertible
   `∂F/∂x` giving a certified order-`N` expansion, with bounds uniform in `ε`
   from Taylor models. The polynomial case does not ship ahead of them.

Probes on the way, logged on the owning issue:

- Is `Hurwitz<Hurwitz<Rat>>` accepted by the class system, so that several
  variables work as iterated series? (step 2)
- What is the kernel cost of a coefficient checked by `refl` through jets
  versus through coefficient functions? (step 2)

Done when the root is an instance of step 6's theorem, checked by the
whole-library gate.

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** (closed): the range sum, the
  antidiagonal, the `∑` binder.
- **[[ring-modulo-a-relation]]** (closed): `ring` at `≈`.
- The issues in `blocked-by` own their layers in full.

## Log

- 2026-10-28: Reworked from a thin first slice (each layer built only as
  far as this result needed) to an acceptance test over the full layers, by
  Minus's decision: the proper design of each layer, not the minimum for one
  case. Step 6 waits for Taylor models rather than shipping the polynomial
  case first.
- 2026-11-01: Step 1 ([[finite-difference-calculus]], closed): layer A′ landed; the residual check `y·y + 8·ε·y − 64 ≈ ε⁴` at `CReal` is `slice_residual` in lib/_tests/std/algebra/difference_tests.hthr. Step 2 ([[formal-power-series]]) first round: the probe "is `Hurwitz<Hurwitz<Rat>>` accepted by the class system" is yes (`nested_one` in hurwitz_tests); Newton doubling for inverses is `Hurwitz::newton_inv_lifts` (order `2^k` after `k` steps, at any commutative ring); Newton for roots of a polynomial is still open there.
