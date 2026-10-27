---
title: Characterise the Gaussian state by Stein's identity
status: open
labels: [mathematics,machine-learning,probability]
area: mathematics
milestone: [ml-gaussian-states]
created: 2026-10-27
updated: 2026-10-27
---

`docs/analysis-foundations-design.md` (§10, §13): characterise the centred
Gaussian state by Stein's identity, which is Gaussian integration by parts,
instead of by its moments.

```
E[x_i · f] ≈ ∑_j C_ij · E[∂_j f]        for every polynomial f
```

The identity determines every moment by induction on degree. In one
variable it gives `E[x^{2k}] = (2k−1)!!·σ^{2k}` and zero odd moments.
Iterated, it produces Wick's sum over perfect matchings. So Isserlis/Wick
becomes a theorem derived from one differential identity, and the identity
ties the Gaussian state to the differential structure, where `∂_j` is the
formal derivative on polynomials.

Scope:

- define the state on polynomials (over `Rat` coefficients, covariance
  `C` a symmetric matrix over `Rat`) by recursion through Stein's identity;
  prove it is a state (linear, `E[1] = 1`) in the sense of
  [[finite-probability]]'s interface;
- prove that it agrees with [[ml-gaussian-states]]' matching definition
  (Wick's theorem as a consequence);
- uniqueness: any state satisfying the identity is this one;
- probes: one-variable moments by evaluation, a mixed fourth moment, and a
  negative control (a non-Gaussian state that fails the identity).

The bridge to a Gaussian measure waits for measure theory, as in
`ml-gaussian-states`.

## What it assumes from elsewhere
- **[[ml-gaussian-states]]** owns Gaussian states, Wick's theorem and
  cumulants. This issue owns only the Stein route and its equivalence.
- **[[formal-power-series]]**: the formal derivative on polynomials.
- **[[finite-linear-algebra]]**: the covariance matrix.
