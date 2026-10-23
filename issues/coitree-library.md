---
title: Coinductive interaction trees with strong bisimilarity
status: closed
labels: [codata,coinduction,itree,library]
area: interaction-trees
milestone: [it-coinductive, it-cotree]
created: 2026-10-22
updated: 2026-10-22
---

`lib/std/itree/coitree.hthr` (`docs/coitree-design.md`): `CoTree<R>(E)` as codata
with observations `Obs`, the combinators written observation-seeded, their
unfolding laws, approximations into `ITree` as a `Program`, and `Bisim` as
indexed codata with refl/sym/trans, the monad laws, a bind congruence and
`Bisim::approx` (bisimilar trees have `Same` approximations).

## What it assumes from elsewhere
- **[[codata-indexed]]** owns indexed codata. Assumed here: only that a
  child writes its own index and `match` refines nothing.
- **[[codata-named-signature]]** owns the spelling. Assumed here: only that
  proofs over `Bisim` cost what they say.

## Log

- 2026-10-22: Done on branch claude/project-thread-lozmdm. Follow-ups: [[coitree-eutt]], [[coitree-program-bridge]]. Met on the way and fixed in the elaborator: an existing function child passed bare (`BVis(c, k1, k2, …, n)`) in a corecursive step was not recognised as a child and reached the kernel unconverted. Not filed: a call nested in a type position, `bind(bind(t, λ r => CRet(r)), λ r => CRet(r))`, does not infer the inner call's result type parameter without explicit type arguments.
