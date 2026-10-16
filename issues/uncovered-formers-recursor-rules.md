---
title: The five uncovered formers' code-recursor branches have no declarative rule
status: closed
labels: [kernel,delam,metatheory,docs]
created: 2026-08-06
updated: 2026-10-16
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

## Log

- 2026-10-16: Closed. Eight of the ten slots now have a declarative rule, written in the Coq formalization (heather-coq, main @ 16ed0d5) from the layer-C typing rules and validated there by `rec_code`; the other two are retired. The statement lives in heather-coq's `theories/Typing/RecSpec.v` rather than `docs/delam-extensions.md`, and `br_calls_derived` checks every branch's calls against its scope. (1) `ty_vec`'s length call: M14b (heather-coq `M14_DESIGN.md`), branches 43–46, agreeing with `rec.rs` slot for slot. (2) `ty_wf`'s, `tm_supf`'s and `tm_elim_wf`'s two `x_S`/`x_M` slots: M15b (`M15_DESIGN.md`, "The four recursor branches, derived from the rules"), branches 47–50, agreeing with `rec.rs` at `b5b2b9d` slot for slot; the one difference is spelling (`ih` at `ℓ'` against `0 ⊔ ℓ'`, the same normalized level). (3) `ty_seq`, `tm_srefl` and `tm_elim_sempty`: M10c (`M10_DESIGN.md`, "M10c outcome"), branches 25, 29 and 30. `ty_seq` and `tm_srefl` have `Id`'s scopes (`(1,4,3)`, `(1,3,2)`), as `rec.rs` says they mirror `ty_id`/`tm_refl`. (4) `tm_transp`'s two slots need no rule: `transp` is being retired from the kernel ([[iwf-former]], design doc §7 and §13 step 6), and the formalization never had the branch (M10c kept the group's six other branches).

  One recorded difference, for whoever next edits these specs: `tm_elim_sempty`'s motive. `rec.rs` (and `typing.rs`) bind `U_M : Typ_c((g, x : sEmpty^{ℓ'} @ ℓ'), ℓ)`, a dependent motive with result `U_M[u_t/x]`, while `docs/sprop-design.md` §2.2 and the formalization have `elim_sEmpty^{l,l'}(M; e) : M` with `U_M` over `g`. The formalization keeps the non-dependent motive. Under irrelevance the two are interchangeable: a dependent `M` is only used at `M[e/x]`, a non-dependent motive, and every instance `M[e'/x]` is convertible to it at D and M. No metatheory change is owed either way; aligning the kernel with the design doc (or the doc with the kernel) is a choice, not a defect.
