---
title: The elaborator's reduction is stuck on a structural recursion arm's hidden children binder
status: open
thread: Refine hypotheses through calls in case splits
labels: [elaborator,matching,recursion]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-17
updated: 2026-11-17
---

Inside an arm of a structural recursion (`emits_runs` in
`lib/native/native_compile_correct.hthr`, the `Invoke(shape)` arm), the
elaborator's whnf of `emits(Invoke(shape), …)` does not reduce, even though
`Invoke` has no recursive field. The scrutinee in the arm is spelled over
the hidden children binder `#rest`, and reduction stops there.

Two things it costs:

- motive synthesis and [[case-split-refines-hypotheses-under-calls]] find no
  stuck test in that arm, so a `match fit: …` there does not refine
  `emitted`, and the arm's proof had to move into a lemma over the inner
  function (`Target::call_runs`);
- any goal in such an arm that needs a call on the arm's constructor
  unfolded is hidden from the reducing rungs the same way.

Found 2026-11-16 while writing #727.

## Wanted

Reduction (or the arm's spelling of its scrutinee) sees through `#rest`
for a constructor whose children the arm does not need, so the call reduces
as it does outside the recursion.

## Done when

`emits_runs`'s `Invoke` arm can carry `call_runs`'s proof inline (the lemma
may stay for readability), and a probe in `lib/_tests` shows a
`match h:` in a recursion arm refining a hypothesis about a call on the
arm's constructor.
