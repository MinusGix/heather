---
title: Multi-index Eventually, additional Directed instances, and Slack proof world
status: open
labels: [stdlib,mathematics,analysis,proofs]
area: mathematics
milestone: [math-reals]
created: 2026-11-24
updated: 2026-11-24
---

Follow-up to [[proof-worlds]] (`lib/std/core/world.hthr`):

1. **More `Directed` instances:** `PosRat` under `>=` (combine by `min`, for ε-δ
   continuity/uniform continuity), finite sets under `⊆` (combine by union),
   and product preorders `Directed<Pair<I, J>>`.
2. **Multi-index `within Eventually for m, n { … }`:** quantify two or more
   directed indices in one block (for Cauchy sequences, double limits, and
   uniform convergence) by pairing indices into a product preorder or chaining
   `Eventually::both`.
3. **Slack / approximation world (`Slack`):** inside-to-outside world for
   `CReal::le_of_slack` / `CReal::same_of_slack` (`∀ m: Nat, lhs <= rhs + 2^-m`
   → `lhs <= rhs`), letting real-inequality proofs split an error budget across
   steps without repeating `CReal::ofRat(Rat::inv_pow2(m))` plumbing.



