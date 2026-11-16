---
title: The elaborator accepts a match arm proved about the unspecialised goal; only the kernel refuses it
status: closed
labels: [elaborator,diagnostics]
area: elaborator
created: 2026-11-11
updated: 2026-11-15
---

When the motive synthesis specialises a goal on a scrutinee that is not a
variable (`match K.eq_dec(k, row.fst) { Inl(hit) => … }`, the goal stuck
on that decision below an `Exists`), an arm written for the goal as it
reads before the split is accepted by the elaborator and then rejected by
the kernel:

```
error: the kernel rejected `List::assoc_get_present`: NotConvertible. this has type
`assoc_get(Cons(row, t), k) = Some(row.snd)`, which does not convert to the type
expected here (that type has no surface spelling)
```

The arm's expected type is `Some(row.snd) = Some(v)`; the proof given has
the unreduced call on its left. The elaborator's check of the arm let the
two meet, so in the arm it treats the scrutinee and the pattern as equal
somewhere the kernel does not. Seen at three library proofs after the
§4.5 rung (`docs/elaborator/goal-motive-synthesis-design.md`): `Bisim::after`,
`List::assoc_get_present`, `StructuredRegion::loop_settles`.

Not unsound: the kernel refuses. The cost is the diagnostic. A kernel
rejection names no surface spelling of the expected type and reads as a
compiler defect, where an elaborator mismatch would have said what the arm
is expected to prove.

## Done when

The three shapes above, kept as probes with the old arms, are refused by
the elaborator with the arm's expected type spelled, or the place the
elaborator identifies scrutinee and pattern is found and the kernel's
motive is built to agree with it.

## Log

- 2026-11-15: Fixed 2026-11-15 (branch claude/project-thread-h1d10i). Not the check: the elaborator records a checking position's two types and the gate decides (`MismatchNotes::note_check_mismatch`), so the old arms were wrong and the kernel was right to refuse. The message was the defect: the arm's expected type is the motive's instance at the arm's constructor, a `case(inl x) { … }` where the scrutinee stood, which the display could not spell. The display now contracts a case on an injection (`spelling::iota_case`, then `contract_projections`), and the refusal reads "but `Some(row.snd) = Some(row.snd)` is expected here". The `assoc_get_present` shapes are kept with the old arms in `lib/_tests/std/core/match_motive_checked_tests.hthr`; goal-motive-synthesis-design §4.6. The related kernel refusal of `if h:` over a measured call's `.after` was a different cause (an ill-typed motive), fixed in the same change.
