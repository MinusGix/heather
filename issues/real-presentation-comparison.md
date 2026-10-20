---
title: Compare real presentations by explicit structure-preserving maps
status: open
labels: [stdlib,mathematics,reals,setoids,axioms]
area: mathematics
milestone: [math-reals]
created: 2026-09-02
updated: 2026-09-02
---

Construct maps among regular Cauchy, located Dedekind, lower, and later localic
presentations, stating exactly which structures each map preserves. Prove
inverse/equivalence results only under the principles actually required, with
directional results retained when a full equivalence is unavailable.

The issue owns the comparison theorems, not the presentations. Its first
acceptance is one nontrivial map plus a transferred abstract theorem and an
assumption inventory. Do not introduce a nominal `Real` equality that erases
constructively meaningful distinctions.

## What it assumes from elsewhere

- **[[setoid-morphisms-and-transport]]** owns generic transport machinery.
- **[[axiom-provenance]]** owns transitive assumption reporting.

## Log

- 2026-09-02: Filed to make interoperability a theorem/API problem rather than
  a demand that every representation share one implementation.
