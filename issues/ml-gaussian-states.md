---
title: Gaussian states, Wick's theorem and cumulants by Möbius inversion
status: open
labels: [mathematics,machine-learning]
area: machine-learning
milestone: [ml-gaussian-states]
created: 2026-10-21
updated: 2026-11-10
---

The algebraic core of PDLT chapter 1, constructively
(`docs/wick-survey.md` §3.4). A moment family is a state `φ : A → R` on a
commutative algebra of observables (Wick's thread T20 refoundation, which
removed its ordered-tuple `Fin.cast` plumbing at the root). A centred
Gaussian with covariance `C` is the state on polynomials whose `2k`-th mixed
moments are sums over perfect matchings of products of `C` entries
(Isserlis/Wick). Cumulants are Möbius inversion of moments on the partition
lattice, with the closed form `μ(σ, ⊤) = (−1)^{k−1}(k−1)!`.

Done when Wick's theorem, moment–cumulant inversion and additivity of
cumulants under independence are proved. The linked-cluster theorem and the
bridge to integration against a Gaussian measure are follow-ups; the bridge
waits for measure theory and nothing here depends on it.

## What it assumes from elsewhere

- **[[set-partition-combinatorics]]** owns matchings and the partition
  lattice.
- **[[finite-probability]]** owns expectation as a state on finite
  distributions. Assumed here: only the state interface.

## Log

- 2026-10-27: Alternative characterisation filed as [[gaussian-state-by-stein]]: the state defined by Stein's identity E[x_i f] = Σ_j C_ij E[∂_j f], with Wick's matching formula as a theorem (docs/analysis-foundations-design.md §13). This issue keeps ownership of Wick's theorem and cumulants.
- 2026-11-10: A convergence statement that lands on this state without measure theory: [[random-walk-gaussian-state]] (docs/continuous-time-survey.md §5.3).
