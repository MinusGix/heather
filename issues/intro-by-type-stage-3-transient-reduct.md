---
title: Intro-by-type stage 3, deferred: does checking against descriptions carry over to the elaborator's transient reduct?
status: open
labels: [elaboration,performance,design,deferred]
area: language
created: 2026-09-22
updated: 2026-09-22
---

Stage 3 of `docs/intro-by-type-design.md` — the elaborator's **transient
reduct**: the elaborator still normalizes a matched type to decide a match
and holds the reduct while it works, even though since stage 2 it no longer
writes it into the term. On 2026-09-22 the item totals on the curve probes
still grew ×1.8/×2.6 per combinator layer after stage 2, and that growth
was stage 3's case.

**Deferred, not dropped** (user, 2026-09-22): after
`docs/app-by-head-type-design.md` the curve is flat enough that stage 3
has no measured subject today. The probes' own theorems, `perf ab` raw
tables, sample 2:

| probe | before app@ | after app@ | queries after |
|---|---|---|---|
| `t_cp9::cp_andt` | 3,536 ms | 118 ms | 15,389 |
| `t_qt3::qt_deep` | 10,399 ms | 264 ms | 20,181 |
| `t_qt5::qt_deeper` | 22,588 ms | 378 ms | 24,973 |

Queries now grow by a constant ~2.4 k per layer, and the elaborator's
share has no exponent visible at five layers. But the library is going to
grow a great deal, and deeper towers than five may appear, so the question
stays open.

**What this issue owns**: decide, when there is a subject, whether the
same methods work on the elaborator's side — checking against a
description instead of holding the spelled reduct, as stages 1–2 did for
the kernel and app@ did for applications. First step when it is picked up:
re-run the curve at more layers (six to eight) and read the elaborator's
phases (`elab_whnf`, `decl_body`, `unify`) per layer, not the kernel gate.

Owning line: [[elab-emits-normal-form-of-matched-type-argument]].
