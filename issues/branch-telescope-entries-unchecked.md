---
title: Branch-telescope entry types are never checked for well-formedness
status: open
labels: [kernel,soundness,testing]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/rec.rs @ HEAD
---

The strongest finding of the [[recursor-elim-call-level-mismatch]] round.
`rec_ga` checks each branch *body* against its instantiated motive type,
but never asks whether the telescope's local entries (`x_M`, `x_t`, …) are
themselves well-formed types under that telescope. That is exactly how an
ill-formed `□(g ⊢ Empty^{ℓ'} @ ℓ)` sat in three branch specs across two
level-indexing rounds: nothing well-formed could be checked against it, so
nothing ever complained — the entry was dead on arrival and silence looked
like health.

## What

A single generic check: for the identity motives, walk
`rec::branch_specs` and `ty_wf` every `tele.locals` entry. It would have
caught all three sites of [[recursor-elim-call-level-mismatch]] at
construction time, and catches the next mis-transcribed telescope entry
generically instead of needing a bespoke observer per branch.
`branch_specs` is `pub(crate)`, so this wants a `#[cfg(test)]` module in
`rec.rs`, not an integration test.

Two narrower follow-ups this check is intended to subsume — take them
separately only if it turns out not to:

- **Witnesses for the `t_elimN`/`t_elim_sE` siblings.** Only `t_elimE` has
  a bespoke regression test; the other two corrected sites are covered
  only by "nothing regressed". `t_elimN` is the rule the Coq formalization
  will transcribe from the paper, so if the generic check stalls, it
  deserves its own observer first.
- **A `□(g ⊢ Ty ℓ)`-motive branch bundle.** The fixtures only carry the
  constant-`Nat` motives and the identity motives, and both are blind to
  the `ℓ`-slot (under the identity motives a mis-levelled entry is
  ill-formed, hence unusable, hence unobserved). An `ℓ`-dependent,
  `U_T`-independent term motive would make the level slots of all 52
  branches *observable* — the fully general witness — at the cost of 52
  hand-written level slots. Well-formedness of entries is the cheap 90%;
  this is the expensive rest.

## When

Next kernel round that touches `rec.rs` or the branch telescopes; or
immediately before the Coq formalization transcribes the `G_Typ`/`G_Trm`
tables, whichever comes first.
