---
title: calc chains over Le/Lt and mixed relations
status: open
labels: [frontend,proofs,design]
created: 2026-08-18
updated: 2026-10-15
---

Residue of [[calc-equational-chains]] (decided out of scope there, 2026-08-18; see docs/calc-equational-chains-design.md par.4). Lean-style calc mixes =/<=/< steps via Trans instances. The designed shape, pinned so the eventual round does not rediscover it: each step carries its relation token, and the fold emits a call on a Trans-class method resolved per adjacent relation pair — exactly as + resolves add through the operator ladder. Not built yet because (1) no library proof wants an inequality CHAIN today (the order kits' transitivity sites are single compositions, one line each); (2) the kit lemmas lack the shape the desugaring needs — trans is pinned by NAMED endpoints, while nat::le_trans is curried/positional and int::le_trans does not even share its calling convention, so the honest prerequisite is a Trans class on the traits layer, not a parser name table over two library-private spellings; (3) the mixed lemmas (=-into-<= transport, < absorbing <= on either side) do not exist and should be demanded by a consumer. Trigger: the first library proof that stalls wanting an inequality chain — record the stall here per the library-drives-features rule.

## Log

- 2026-10-14: Trigger hit: `two_halves_close` in docs/showcase/rat_client.hthr ([[rational-order-completion]]) is a three-step `≤` chain (`dist_triangle`, then `≈` into `half + half`, then `inv_succ_half`), written as nested `Rat::le_trans`/`Rat::le_respects`. The mixed lemmas now exist at `Rat` (`lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_respects`, `lt_respects`), and `Rat` registers `Transitive` for both `Rat::Le` (via `Preorder`) and `Rat::Lt`.
- 2026-10-15: Rat style review (PR #42): after making the order transports' endpoints implicit, what is left of `dist_triangle` and `abs_triangle` is exactly 'rewrite each side by ≈, then chain ≤', which an order calc would state as the textbook proof.
