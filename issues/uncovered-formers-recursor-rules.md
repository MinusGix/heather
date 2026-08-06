---
title: The five uncovered formers' code-recursor branches have no declarative rule
status: open
labels: [kernel,delam,metatheory,docs]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/rec.rs @ HEAD
---

The sequel to the closed [[delam-extensions-writeup]], surfaced by
[[branch-telescope-type-motive-level-slots]]. That round enumerated all 45
type-motive recursive-call slots and found 10 with no declarative rule to
check against: the code-recursor branches of the five formers
`docs/delam-extensions.md` §17 deliberately left uncovered —
`ty_vec`, `ty_wf`, `tm_supf`, `tm_elim_wf` (×2), `ty_seq`, `tm_srefl`,
`tm_transp` (×2), `tm_elim_sempty`.

For those ten, the in-suite checks still validate call-against-binding
(the right *relation*), but nothing outside the kernel attests the
*binding*: the kernel is its own only specification. That is exactly the
state `t_elimE` was in before the writeup round, and `t_elimE` turned out
to be transcribing a paper typo — with no paper here, an original mistake
would have nothing to be caught against.

## What

Extend `docs/delam-extensions.md` (or a sibling section) with the
declarative `G_Typ`/`G_Trm` telescope rules for the `Vec`/`Fin`/`Wf`/
`sEq`/`sEmpty` code-recursor branches, in the same style as the six
formers' §10 tables — written from the semantics, then checked against the
kernel, so the direction of authority is right.

## When

Before the Coq formalization transcribes `G_Typ` — the ten unattested
slots are precisely where a transcription error would be invisible on both
sides. Or the next edit to any of those branch specs.
