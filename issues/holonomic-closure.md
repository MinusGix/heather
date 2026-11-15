---
title: Holonomic functions and sequences with closure certificates
status: open
labels: [tactics,mathematics,analysis]
area: tactics
created: 2026-10-27
updated: 2026-10-27
---

`docs/library/analysis-foundations-design.md` §3.5: holonomic (D-finite and
P-recursive) objects, meaning functions and sequences given by a linear
ODE or recurrence with polynomial coefficients plus initial terms, closed
under `+`, `·` and some compositions, with identities proved by comparing
finitely many coefficients.

Scope:

- representation over Hurwitz series: an annihilating operator and initial
  terms; uniqueness of a solution with given initial terms by coinduction
  (§3.4);
- closure certificates for sum and product (the operator for the result,
  checked as an operator identity by `ring`);
- probes: `sin² + cos² ≈ 1` and `exp(a·t)·exp(b·t) ≈ exp((a+b)·t)` by
  certificate rather than by hand; a recurrence identity (Fibonacci or
  harmonic-type);
- interplay with [[wz-certificates]] (creative telescoping is the
  holonomic summation step).

## What it assumes from elsewhere
- **[[formal-power-series]]**: Hurwitz series and the coinduction principle.
- **[[wz-certificates]]**: the certificate-checking route.
