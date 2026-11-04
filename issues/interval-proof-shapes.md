---
title: Make interval.hthr's proofs read as their arguments (APIs and automation)
status: closed
labels: [reals,intervals,stdlib,tactics]
area: mathematics
created: 2026-10-30
updated: 2026-10-30
---

Minus (2026-10-30): which APIs or tactic automation would make
`lib/std/num/float/interval.hthr` more elegant, given the repeated
`le_respects` chains and logic that looks automatable. The analysis, with
before/after for each shape, is `docs/interval-proof-shapes.md`.

Done in the round: one-sided `≈` steps (`Rat::le_of_same_of_le`,
`le_of_le_of_same`), `Interval::bnd_has_of` and `round_out_has`, written
motives dropped where synthesis finds them, one `IntervalExpr::search` for
both orders, `Bool::is_true_of_eq`, `calc` for `of_rat_same`, and the small
missing facts (`Rat::mul_le_mono_l_nonpos`, `Dyadic::rat_nonneg`,
`neg_pos`, `lt_of_not_le`).

Left, ranked in the doc: [[elab-match-refines-hypothesis-kernel-rejects]]
(the convoys over `Whole`), [[interval-containment-once-over-ordered-field]],
[[push-cast-through-embeddings]], [[one-sided-respects-sweep]]. Found:
[[and-at-match-predicate-implicit-level-mismatch]].
