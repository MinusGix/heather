---
title: Find linarith's combination by exact simplex instead of Fourier–Motzkin
status: open
labels: [tactics,arith,solver]
area: tactics
milestone: [tac-arith]
created: 2026-10-28
updated: 2026-10-28
---

`linarith` finds its multipliers by Fourier–Motzkin elimination and gives up
past 2048 rows (docs/linarith-design.md §3). The elimination is doubly
exponential in the worst case. `nlinarith` grows the input from `k` rows to
`k + k(k+1)/2` and adds monomials, so the row bound is the first limit it
will meet (docs/nonlinear-arithmetic-design.md §6).

Exact simplex over ℚ finds the same Farkas multipliers: rows scaled to `Z`,
Bland's rule against cycling, and `λ` read off the final tableau. It is
polynomial in practice. Mathlib replaced `linarith`'s Fourier–Motzkin oracle
with simplex for this reason. The certificate does not change. The search is
untrusted, the combination is recomputed and checked in Rust before it is
written (as now), and `ring` checks the identity.

Open choice for the round: replace Fourier–Motzkin, or keep it for small
problems, where it is simple and its "strongest row per linear part" pruning
is cheap. Decide by measuring with `scripts/perf ab` on the `linarith`
probes, since this round's point is performance.

No customer yet. The first `nlinarith` refusal at the row bound is one.

## What it assumes from elsewhere

- **[[nlinarith-products-of-facts]]** owns the product rows. Assumed here:
  only that they are rows like any other.

## Log

- 2026-11-05: gardener: cites a file it shares with [[interval-variable-boxes]] (`docs/nonlinear-arithmetic-design.md`); [[sos-certificate-oracle]] (`docs/nonlinear-arithmetic-design.md`).
