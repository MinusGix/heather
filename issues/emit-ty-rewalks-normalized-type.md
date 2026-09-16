---
title: The emission chokepoint re-walks the type the elaborator has just normalized: seconds per constructor value on the parser family
status: open
labels: [elaboration,performance]
created: 2026-09-16
updated: 2026-09-16
---

Found by the `HEATHER_NF_SPIKE` instrument of docs/conversion-query-traversal-design.md §10 (2026-09-16, probes/nf_spike.patch). `Elaborator::emit_ty` reached through `respell_spine` under `build_ctor` spends **505 ms** (probes/t_cp9, `cp_andt`), **1 130 ms** (`parser_primitives::complete_post`) and **2 989 ms** (probes/t_qt3, `qt_deep`) walking a single constructor value's Σ/Sum spine — more than the `whnf` that built that spine (492.6 / 986 / 2 213.5 ms) — and returns a rewrite each time. On this family that is a second full traversal, per constructor value, of an object whose size is the subject of [[elab-emits-normal-form-of-matched-type-argument]]. Constant-factor and downstream of that exponent: it cannot be the answer there, and banking it would retire the evidence (design §5's own argument against the typed-App rule). What is worth asking on its own: whether the component walk can decline early on a spine whose components cannot respell, and whether the spine's components are walked once per constructor value that shares them. Measure with the spike patch and `--timings` (the `item=` scope only exists under it). Related: [[elab-emits-normal-form-of-matched-type-argument]], [[emission-spelling-chokepoint]].
- 2026-09-16: Second customer and sharper statement (docs/projected-tuple-tower-design.md §10): the chokepoint's walk is one of three full traversals of the same exponential object (rewriter, chokepoint, kernel); candidate D would have made it four.
