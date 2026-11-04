---
title: A differential-structure interface: maps with derivative evidence, forward and reverse
status: open
labels: [stdlib,mathematics,analysis,design]
area: mathematics
milestone: [math-reals,ml-layers]
created: 2026-10-27
updated: 2026-10-27
---

Axis 1 of `docs/analysis-foundations-design.md` (§3.1): one interface for
"a map with its derivative", so the chain rule and its relatives are laws
stated once and every instance (jets, Hurwitz series, `C¹` on `CReal`,
Lipschitz with interval derivatives, programs, ML models) inhabits them.

Scope:

- the encoding decision (§14, left open): a class over an evidence
  predicate on plain functions (`Diff<A, B> { map, deriv, ok }`), or over a
  category record; the first is expected to be enough for the Cartesian
  case;
- the Cartesian differential axioms (Blute–Cockett–Seely) as the interface's
  laws: additivity, linearity in the direction, identities and projections,
  pairing, chain rule, symmetry of second derivatives;
- a reverse form `R[f]` (reverse derivative categories) with the
  forward/reverse relation, for `ml-layers`;
- smoothness as derivative evidence at every order (§3.1: `C^∞` is
  coinductive, `C^k` is `k` unrollings);
- first round's two instances (§3.7): polynomial maps with the formal
  derivative, and Hurwitz series with the shift; the `C¹` `CReal` instance
  follows [[certified-expansions]];
- the lax instance (chain rule as an inclusion) for Lipschitz maps with the
  Edalat–Lieutier derivative: state what the interface weakens to.

Tangent categories (non-Cartesian spaces) are out of scope until a
manifold customer.

## What it assumes from elsewhere
- **[[formal-power-series]]**: polynomials, jets and Hurwitz series.
- **[[real-functions-and-derivatives]]** owns the `CReal` derivative; this
  issue owns the interface it instantiates.
- **[[ml-layers-reverse-mode]]**: the reverse-mode customer.
