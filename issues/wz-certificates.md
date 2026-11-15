---
title: Prove hypergeometric sum identities by WZ certificates
status: open
labels: [tactics,mathematics,analysis]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

`docs/library/analysis-foundations-design.md` §3.5: prove hypergeometric finite-sum
identities by checked certificates (Gosper, Zeilberger, Wilf–Zeilberger
pairs; *A = B*), the analysis counterpart of `omega` and `ring`.

Scope:

- the certificate: a rational function `R(n, k)` such that `F(n+1, k) -
  F(n, k) = G(n, k+1) - G(n, k)` with `G = R·F`; checking it is a rational
  function identity (clear denominators, then `ring`), plus the telescoping
  lemma of [[finite-difference-calculus]] and boundary terms;
- the search can be untrusted and outside the kernel (Rust or an external
  oracle), as long as the check is kernel-checked;
- side conditions: denominators nonzero on the summation range, discharged
  by `omega` at `Nat`/`Int` or reported;
- probes: `∑ C(n,k) = 2^n`, Vandermonde, `∑ C(n,k)² = C(2n,n)`, and a
  refusal with a wrong certificate.

The holonomic generalisation (ODE- and recurrence-defined objects) is
[[holonomic-closure]].

## What it assumes from elsewhere
- **[[finite-sums-and-products]]** and **[[finite-difference-calculus]]**:
  range sums, telescoping, binomial coefficients.
- **[[field-simp]]**: clearing denominators before `ring`.
