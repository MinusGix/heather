---
title: Branch-telescope entry types are never checked for well-formedness
status: closed
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

## Done

`crates/kernel/src/rec.rs` — a `#[cfg(test)]` module walking both motive
telescopes and all 52 branch telescopes: each telescope's global bindings
as a Ψ (`check_global_ctx`), then every `tele.locals` entry as a type at
its declared level under the prefix that precedes it, in the scope
`push_spec` really builds — `univs + tele.univs`, Ψ extended by the
telescope's globals, Γ extended by the preceding entries, at layer `m`
(`rec_ga` runs under `meta_layer`, and every entry is a `□(…)`, which no
lower layer admits). The branch's own expected type is checked while we
are there: an ill-formed one is unsatisfiable in the same silent way, and
was equally unchecked. `BRANCH_NAMES` lets a failure say which branch and
which entry index without formatting a term.

**The identity motives are the sharper observer, and it is worth saying
why.** `M_Trm[l/ℓ, …, U/U_T, …]` instantiates to `□(g ⊢ U @ l)`, whose
well-formedness *is* the judgment `g ⊢ U @ l` — the `U_T` slot and the `ℓ`
slot are forced into agreement, which is exactly the defect class of
[[recursor-elim-call-level-mismatch]]. A `U_T`-ignoring motive would make
the same entry well-formed and so invisible here. The two motive families
are complementary, not ordered: identity is sharper for *formation*, `Ty ℓ`
for *use*.

Polarity verified by reintroducing each of the three corrected sites in
turn: `tm_elim_empty` entry #1, `tm_elim_nat` entry #3, `tm_elim_sempty`
entry #1, each failing `LevelMismatch` under its own name, each restored.
The `t_elimN`/`t_elim_sE` witness follow-up is thereby discharged —
`tm_elim_nat`'s old entry is `□(g ⊢ Nat @ ℓ)` and `Nat` lives at `0`, so a
universe variable in that slot is caught at formation. No currently
ill-formed entry anywhere in the tables. Suite 1134 → 1135, full
`scripts/test` green, no golden number moved.

**Residue.** The `□(g ⊢ Ty ℓ)`-motive bundle is *not* subsumed, for a
sharper reason than the one filed above. Type-motive entries instantiate to
`□(g ⊢ Ty l)`, well formed for *any* in-scope `l`: the level's scope is
checked, its value is not. Mutating `ty_pi`'s `x_S` slot from `ℓ` to `ℓ'`
leaves this check green — probed, not assumed. And no motive can fix it:
`x_T` occurs in `M_Typ` only as a local of contextual type and there is no
type-level unboxing, so `ℓ` and the `x_T` payload can never meet inside the
motive. The level slots of `x_S`/`x_T`/`x_M` are observable only by a
bundle whose *bodies* use their recursive calls.
[[branch-telescope-type-motive-level-slots]]. A second, smaller residue:
the check is a test, so the kernel proper still trusts the tables at
runtime — [[rec-ga-runtime-telescope-check-decision]]. And the round's
stray observation — the tree is not fmt-clean and no rule says whether it
should be — is filed at [[fmt-not-enforced-decision]].
