---
title: Unify through a rigid head mismatch by the kernel's δ-lazy order, not retries
status: open
labels: [unification,inference,elaboration]
area: language
created: 2026-11-02
updated: 2026-11-02
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
