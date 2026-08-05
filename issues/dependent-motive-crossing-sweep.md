---
title: Sweep the case-tree lowerings at the dependent-motive crossing
status: open
labels: [elaboration,inductives,testing]
created: 2026-08-05
updated: 2026-08-05
---

From the equation-binding round (2026-08-05), which found and fixed a live shift defect in tier-0 `inductive.rs::case_tree`: the inner injection's summand annotations were shifted `d + 1` where the context is two binders deep (`d + 2`). Same defect the 2026-08-04 round fixed in `wf_case_tree`/`idx_case_tree`/`indexed_case_tree` — and missed here, because every existing tier-0 test at 3 ctors × open payload used a *non-dependent* motive, where `z` never occurs and the bad annotations are substituted away before the kernel sees them.

That refined axis 6 of docs/testing-generated-terms.md (doc updated in that round): the crossing needs **three** conditions — ≥3 constructors × open payload × **dependent motive**. `match h : e` makes a motive dependent by construction, so it is the cheap way to drive the crossing.

The sweep this issue owns: run the 3-way crossing over the `Wf`, indexed and forded lowerings' *own inner nodes* (their 2026-08-04 fixes were found by a different route and their test crossings may have the same gap tier-0's did). One round; expected outcome is either regression tests that pin the crossing everywhere, or another shifted annotation.
