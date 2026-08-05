---
title: Sweep the case-tree lowerings at the dependent-motive crossing
status: closed
labels: [elaboration,inductives,testing]
created: 2026-08-05
updated: 2026-08-05
---

From the equation-binding round (2026-08-05), which found and fixed a live shift defect in tier-0 `inductive.rs::case_tree`: the inner injection's summand annotations were shifted `d + 1` where the context is two binders deep (`d + 2`). Same defect the 2026-08-04 round fixed in `wf_case_tree`/`idx_case_tree`/`indexed_case_tree` — and missed here, because every existing tier-0 test at 3 ctors × open payload used a *non-dependent* motive, where `z` never occurs and the bad annotations are substituted away before the kernel sees them.

That refined axis 6 of docs/testing-generated-terms.md (doc updated in that round): the crossing needs **three** conditions — ≥3 constructors × open payload × **dependent motive**. `match h : e` makes a motive dependent by construction, so it is the cheap way to drive the crossing.

The sweep this issue owns: run the 3-way crossing over the `Wf`, indexed and forded lowerings' *own inner nodes* (their 2026-08-04 fixes were found by a different route and their test crossings may have the same gap tier-0's did). One round; expected outcome is either regression tests that pin the crossing everywhere, or another shifted annotation.

## Log

- 2026-08-05: Swept (managed round). All five case-tree emitters audited for the inner-injection shift; **all shifts were already correct**, so the round's output is the missing controls plus one unrelated defect the controls uncovered. Regression tests at the level each term is generated: `inductive_tier1.rs::an_inner_wf_injection_is_scoped_two_binders_deep` (wf_case_tree), `indexed_families.rs::an_inner_class_injection_is_scoped_two_binders_deep` + controls (indexed_case_tree), `indexed_route_2b_gen.rs::the_forded_case_trees_inner_injection_is_scoped_two_binders_deep` + controls (idx_case_tree at the forded non-recursive-skeleton caller). Each verified by mutation (d+2 → d+1) to be the *only* failing test in its area; symptom LevelMismatch every time. Two emitters need no dependent-motive condition — wf_case_tree's motive and the forded q are dependent by construction — so the 2026-08-05 axis-6 refinement bites exactly where the motive comes from the surface: tier 0 (fixed 2026-08-05) and indexed_case_tree (now pinned). Two idx_case_tree callers are structurally blind and can never carry the defect: build_mu (constant motive) and the flat declared-index route (an index declaration may not have type parameters, so its spine is closed). Measured aside: wf_case_tree's crossing was in fact covered — by indexed_route_2b_gen.rs, four layers above the emitter. Fixed en route (narrative on [[indexed-families]]): forded.rs::ctor_spine_at re-lowered the skeleton at no type arguments, making every parameterized forded family with a non-recursive skeleton unusable; the axis-2 control could not be written until it was fixed — docs/testing-generated-terms.md gains the corollary: two conditions each tested alone is not evidence their product works. Suite 1059 → 1064.
