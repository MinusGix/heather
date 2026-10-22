---
title: Equivalence up to taus (eutt) on coinductive trees
status: closed
labels: [codata,coinduction,itree,library]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-10-22
---

Strong bisimilarity (`Bisim`, `lib/std/coitree.hthr`) relates trees step for
step, so `CTau(t)` is not related to `t`. Weak bisimilarity lets either side
peel finitely many `CTau`s before the next visible step, which is what
program equivalence needs (`iter`'s productive `CTau` per pass, and the
`bind` laws of the effect handlers).

Kernel design §4 (`docs/kernel-coinduction-design.md`) spells it as an `M`
whose shape is an inductive peel: an index is a pair of trees, a node is an
inductive proof that both sides reach matching observations after finitely
many taus, and the children are the matched subtrees. With indexed codata
(`docs/codata-indexed-design.md`) the surface version is a `codata` over
`(t, u)` whose constructor carries an inductive `Peel` field.

Done when: `Eutt` with refl/sym/trans (trans is the hard one: peeling
through the middle tree), `Bisim → Eutt`, `CTau(t) ≈ t`, the monad laws up
to eutt, and `Eutt` giving equivalent approximation programs (with
[[coitree-program-bridge]]).

## What it assumes from elsewhere
- **[[coitree-library]]** owns `CoTree`, `Obs` and `Bisim`. Assumed here:
  only the observation-seeded style (`docs/coitree-design.md` §2).

## Log

- 2026-10-22: Done (`lib/std/coitree_eutt.hthr`, `docs/coitree-design.md` §7). Drops are counts, not an inductive peel: each constructor names how many `CTau`s each side drops (`CoTree::after`). refl/sym/trans, `of_bisim`, `tau_l`/`tau_r`, the monad laws (through `of_bisim`), and `Eutt::refines`/`refined` (equivalent trees give programs that refine each other). The `bind` congruence up to eutt is left to [[coitree-eutt-bind-cong]]. Making it cheap needed a codata change: a match's payload fields are now checked-spelling projections (`docs/codata-named-signature-design.md` §8).
