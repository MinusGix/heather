---
title: Design proofs that compose against interfaces, and modular automation
status: open
labels: [design,proofs,elaboration,tactics]
area: language
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-10-31
---

Round P1 of `docs/native/compiler-milestones-proposal.md` (§6, §7): the design round for `lang-proof-modularity`.
Minus asked on 2026-10-31 that proving a specific property should not
need thinking about lots of code, and that automation be modular for
reasoning and for cost.

## Scope

- Interface definitions (proposal §6.3). Minus decided on 2026-10-31 that they are opt-in per definition. The note settles what the elaborator and tactics may unfold, where, the `unfold f` escape, the generated equations, and how this meets closed evaluation and boxing.
- One registry mechanism that tactics read through the host interface (`mono`, `norm_num`, ring atoms, rewrite sets), and which tactic reads it first.
- Invariant rules for loops and contracts for procedures (with [[sequencing-surface-design]] and [[native-procedure-contracts]]).
- Sharing and staging: what [[frontend-large-proof-composition-cost]] and [[let-fanout-diagnostic]] need.
- For each piece, which rule in `docs/proof-patterns.md` it retires.

## Done when

Minus has decided the note, and [[interface-definitions]], [[automation-lemma-registries]] and [[loop-invariant-rules]] state their scope against it.
