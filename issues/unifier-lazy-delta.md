---
title: Unify through a rigid head mismatch by the kernel's δ-lazy order, not retries
status: open
labels: [unification,inference,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-03
---

When two rigid heads differ, the elaborator's unifier learns nothing
(the distinct-heads and spine-length guards), and callers retry on a proxy:
`unify_arg_ty` whnfs the argument type only when the first read "learned
nothing", #387 added "or a solution was rejected" plus 8 reducts, and
[[argument-type-reduction-after-partial-inference]] asks for "or partial
progress, but not always". The kernel's own conversion is δ-lazy
(crates/kernel/DESIGN.md: same head → compare spines; otherwise unfold to
δ-heads and compare again). The unifier is learn-only conversion with metas
and does not follow that order (docs/elaborator-principles-survey.md §3.2).

## Proposal (P3)

At a rigid–rigid head mismatch inside `unify_tm`, unfold to δ-heads (one δ
step at a time, global heads only, at the elaborator's transparency, so
`interface fn` stays opaque) and compare again, recording solutions where
conversion would compare a meta. Definitional heights (one plus the maximum
over the globals a body mentions, in the module image) are an optional
refinement that picks which side to unfold. Then delete the whnf retries in
`unify_arg_ty` and `solve_from_expected` and `INDEX_UNFOLD_STEPS` once the
library passes without them.

## Expected to close or retire

- [[argument-type-reduction-after-partial-inference]]
- [[unifier-spine-across-distinct-heads]] (its second reading: `pick(h)`
  elaborates)
- [[decide-at-defined-proposition]], once instance heads use the same
  unifier ([[instance-conclusion-matched-first]])

## Cost and risk

Unfolding in the elaborator is the known cost (computed types: "elaborator
whnf is the cost"), so the step is local to a mismatch and one δ at a time,
and the round measures with `scripts/perf ab`. More solutions are found, so
some library calls elaborate differently; the library gate is the check.

Depends on [[unifier-checked-assignment]] (so an unfolding cannot commit a
wrong-typed solution) and is easier after [[one-unfold-to-primitive]].

## Log

- 2026-11-03: Built (subject side). Wherever a pattern and a subject do not meet as they stand — two rigid spines with different heads or lengths, a former against `El` of a computed code, or any other pairing the congruence has no rule for — the unifier unfolds the subject to its next head (`U::next_head`: δ, then the β and ι steps that expose what the body is headed by, at most `Unfold::NextHead` head reducts per hop) and compares again (`unify_unfolded`). Only while the pattern still has an open slot (so a closed verdict is never evaluated for nothing) and only a subject headed by a global, a λ or an eliminator. Only the subject unfolds: the pattern mentions this call's metas, which no world here declares, and learning from a reduct of the subject learns what conversion with it would. Heights are not used. `unify_arg_ty`'s whnf retry is deleted: the whole library re-elaborates without it (`heather check -L lib --expectations lib`, 262 expected refusals matched). `solve_from_expected`'s whnf of the expected type stays: with it deleted, `Bind::seq`'s higher-kinded carrier (`?M(?B)` against `Tac<Nat>`) went unsolved in mono.hthr, regex.hthr and binding_statements_tests, which is a spelling question (respell/slot_view), not δ. `Unfold::IndexRead` also stays: its trigger is a flex head whose write was refused for its type, which this step does not read. Probe: lib/_tests/std/core/bool_tests.hthr `lazy_delta_pick_through_g`; Rust: crates/elab/tests/unifier_lazy_delta.rs.
