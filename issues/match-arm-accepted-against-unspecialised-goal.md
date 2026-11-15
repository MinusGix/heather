---
title: The elaborator accepts a match arm proved about the unspecialised goal; only the kernel refuses it
status: open
labels: [elaborator,diagnostics]
area: elaborator
created: 2026-11-11
updated: 2026-11-11
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

- 2026-11-15: Likely a fourth shape in the sort example: an `if h: i < n` over a goal mentioning a measured `mut self` call's `.after`, worked around there; [[theorem-branch-on-measured-fn-goal]].
