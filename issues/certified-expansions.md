---
title: Expansions in a scale with a certified remainder
status: open
labels: [stdlib,mathematics,analysis,reals,design]
area: mathematics
milestone: [math-reals]
created: 2026-10-27
updated: 2026-10-27
---

Layer D of `docs/analysis-foundations-design.md` (§7): an expansion in a
scale with a certified remainder, read either uniformly on a neighbourhood or
asymptotically, and the derivative defined as a uniform first-order expansion.

Scope:

- the `Expansion` record (coefficients, remainder constant and neighbourhood,
  the bound) and its asymptotic projection to `O(φ_N)`;
- operations as pairs: jet arithmetic for the coefficients and a closure lemma
  for the remainder; the jet map is a ring homomorphism into `Jet(F, N)` and
  sends composition to composition;
- the `asymp` tactic shape (normalise `O`-terms, certificate = closure lemmas),
  designed here, built when the lemmas exist.

This issue owns the record and its algebra.
[[real-functions-and-derivatives]] owns the derivative built on it, and
[[taylor-model-enclosures]] owns the uniform reading over interval domains.

## What it assumes from elsewhere
- **[[asymptotic-relations]]**: approaches and the `O`/`o` algebra.
- **[[formal-power-series]]**: jets.
