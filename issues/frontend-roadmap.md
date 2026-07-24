---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-07-24
---

Organizing issue for the frontend push (the frontend-first route,
[[elaborator-design]]). The point of this issue: keep the *focus order*
here so the per-topic issues stay granular and jumpable — pick any issue up
without re-deriving where it sits.

Design record: [[surface-syntax]] (decisions) + docs/sketches/surface-v0..3
(the reasoning); requirements tracker: [[front-end-sugar]].

## Focus order (edit as reality intervenes)

1. ✅ Stage 1: parser + annotation-filling elaborator; Nat suite checked
   ([[elaborator-design]], [[stress-proof-suite]] item 1).
2. [[metatheory-ch07-pass]] — interleave; wants doing before tier-1
   inductives generate serious term volume on the extension formers.
3. ✅ [[elab-stage2-metas]] — implicit annotations/levels; the Nat suite loses
   its explicit motives and endpoint spam. Unblocks most ergonomics.
4. ✅ [[surface-operators]] — `+`/`==` operators, method calls, `calc`.
   Mostly parallel to 3; lemma-application ergonomics.
5. ✅ [[match-recursion]] — termination checking; `induction`/`rec` collapse
   into `match` with IH = self-call.
6. [[goal-holes]] — `?holes` + `on` discharge (needs stage-2 metas).
7. [[inductive-compiler]] tier 0 → List hand-prototype → tier 1
   ([[stress-proof-suite]] item 2).
8. Tier 2 / `Acc` by hand ([[stress-proof-suite]] item 3), then reopen
   [[ir-simulate-design]] in-language.

Later, tracked where linked: implicit quotation + modal surface
([[surface-syntax]] round 2), context-specific compilation / certified PE
([[compile-typeclass-design]], [[certifying-generator]] — sketch round 3),
goal-solver meta-functions (sketch round 3 §2).

## Log

- 2026-07-23: Opened after stage 1 landed, alongside the granular issue
  split (stage2/match-recursion/goal-holes/surface-operators/ch07-pass).
- 2026-07-24: Stage 2 ([[elab-stage2-metas]]) landed — focus items 3 (metas/motives) done for the level-0 Nat suite. Level-meta *inference* deferred: no level constraints exist below layer m (universe polymorphism is layer-m only), so it is naturally sequenced with the later modal/layer-m work, not with stage 2. Next focus: item 4 [[surface-operators]] (+/== operators, method calls, calc) — now unblocked and high-leverage on top of implicit endpoints — interleaved with item 2 [[metatheory-ch07-pass]] before [[inductive-compiler]] term volume.
- 2026-07-24: Deferred stage-2 unifier work promoted to a jumpable item: [[elab-unifier-completeness]] (postponement, general pattern inversion, level-meta inference). Kernel-gated, none are correctness holes; pick up when a program needs them.
- 2026-07-24: Item 4 [[surface-operators]] landed (operators/methods/calc as parser desugaring). Deferred within it, tied to later work: higher-order .cong(Succ) needs first-class function values/types in the surface (part of the trait/function-value layer, [[compile-typeclass-design]]); mul/lt need defs. Next focus: item 5 [[match-recursion]] (unified self-call match, drops the explicit Succ(k, ih) binder) and item 2 [[metatheory-ch07-pass]] before [[inductive-compiler]] term volume.
- 2026-07-24: Filed [[surface-proof-automation]] (user-requested, unscheduled): auto-refl (empty-block trivial-closer; independent tiny MVP) + apply (prefix continuation application; wants goal-holes' block-statement surface). Sits after/with [[goal-holes]] in the 'later' cluster.
- 2026-07-24: Equality notation settled ([[surface-syntax]]): single `=` for binding + propositional equality (ML-style), `==` rejected with a hint, `:=` for discharge (and future assignment, [[effects-direction]]). Follow-up diagnostic tracked: [[warn-bare-eq-no-effect]].
- 2026-07-24: Item 5 [[match-recursion]] landed: unified `Succ(k)` match with IH = guarded self-call; Nat suite now readable as recursive theorems. Deferred within it: generalizing a *varying* non-decreasing argument into the motive (rejected with a diagnostic; additive to add later). Next focus: item 2 [[metatheory-ch07-pass]] before [[inductive-compiler]] term volume, then item 6 [[goal-holes]].
- 2026-07-24: Item 2 [[metatheory-ch07-pass]] done and closed: full ch. 07 pass over the six extensions (docs/metatheory-ch07-extensions.md), nothing broken, no kernel-rule change, so [[inductive-compiler]] tier 1 is no longer gated on unpaid metatheory debt. Next focus: item 6 [[goal-holes]], then item 7 [[inductive-compiler]] tier 0.
- 2026-07-24: Item 6 [[goal-holes]] landed: `?name`/`?` holes as decl-scoped Ψ-metas, `on ?name := e;` / `on _: P := e;` discharge, and the unsolved-goal listing (with the first `Display for ElabError`). Came with the block-statement grammar the roadmap had been deferring — `Block` + `let` — which is the surface [[surface-proof-automation]]'s `apply` was waiting on, so its cheap slice is now unblocked too. Deferred within it, each tested as a rejection: holes are checking-only (so `sym(?p)` needs `@sym(a,b,?p)` — the fix is postponement, i.e. [[elab-unifier-completeness]], not this issue), one occurrence per named hole, no holes inside an `on` RHS (goal payloads are not telescoped), `on` trailing-only, and auto-defer holes (`xs[i]`) still want the trait/indexing layer. Next focus: item 7 [[inductive-compiler]] tier 0 → List hand-prototype → tier 1 ([[stress-proof-suite]] item 2).
