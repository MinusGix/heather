---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-07-26
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
2. ✅ [[metatheory-ch07-pass]] — interleave; wants doing before tier-1
   inductives generate serious term volume on the extension formers.
3. ✅ [[elab-stage2-metas]] — implicit annotations/levels; the Nat suite loses
   its explicit motives and endpoint spam. Unblocks most ergonomics.
4. ✅ [[surface-operators]] — `+`/`==` operators, method calls, `calc`.
   Mostly parallel to 3; lemma-application ergonomics.
5. ✅ [[match-recursion]] — termination checking; `induction`/`rec` collapse
   into `match` with IH = self-call.
6. ✅ [[goal-holes]] — `?holes` + `on` discharge (needs stage-2 metas).
7. ✅ [[inductive-compiler]] tiers 0 and 1 — the latter onto `Wf`, not
   fording; [[stress-proof-suite]] item 2 done. The issue itself stays open
   for tier 2 and the surface gaps ([[nested-inductives-container-fields]]).
8. [[surface-function-types]] — dependent `->` and `λ`; the surface type
   grammar is three constructors wide and this is what widens it. No kernel
   change (Π/λ/App are v0), so no metatheory round.
9. [[nested-inductives-container-fields]] — container field types (`Rose`),
   which is what any IR needs and what finite sequences need on the
   mathematics side. Smaller once 8 lands: the fold is an ordinary function.
10. Tier 2 / `Acc` by hand ([[stress-proof-suite]] item 3) — note `Acc` is
    not *stateable* at the surface until 8, so this is a kernel-level test of
    the synthesized-ih β rule, not frontend progress. Then reopen
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
- 2026-07-24: Item 7 [[inductive-compiler]] TIER 0 LANDED: scheme doc first (docs/inductive-tier0-lowering.md), then the mechanization (crates/elab/src/inductive.rs) plus surface support — 'inductive' decls with monomorphized type parameters, named/applied types, n-ary match arms (Nat folded into the same grammar), constructors in both modes, and no-confusion as 'absurd(p)'/'inj(k, p)'. 24 acceptance tests, every one kernel-checked. Two scheme corrections found by implementing: the nominal tag must be eta-irrelevant (Sigma-of-Units, not Id — a dependent motive needs 'inl x' to convert with the canonical constructor), and injectivity needs no large elim (the lhs's own field is the default, which keeps the motive constant and drops the level restriction). Deferred and diagnosed rather than mis-lowered: tier 1 (recursive) declarations, dependent-field injectivity, deep type-argument inference. Next focus: item 7's remainder — the List hand-prototype (exact-height fording) as the acceptance test for tier 1 ([[stress-proof-suite]] item 2), then the tier-1 generator.
- 2026-07-26: Item 7 remainder closed on the linear side: [[stress-proof-suite]] item 2 is DONE — append_nil/append_assoc/rev_append written at the surface over a generator-produced 'inductive List' and kernel-checked (crates/elab/tests/tier1_list_proofs.rs). The tier-1 generator needed no changes to carry proof content, only definitions, which was the open question. Next focus: item 8 — tier 2 / Acc by hand ([[stress-proof-suite]] item 3), which exercises the synthesized-ih beta rule, the least battle-tested kernel machinery; then [[ir-simulate-design]] reopens in-language.
- 2026-07-26: Focus order revised after a direction review. Items 8-10 were 'tier 2 / Acc, then the IR'; they are now [[surface-function-types]], then [[nested-inductives-container-fields]], then Acc. Reasoning: (1) Acc is not on the critical path — [[ir-simulate-design]] specifies a FUEL-INDEXED simulate, so it recurses on Nat, and the IR is first-order data that tier 1 already covers; nothing before [[end-to-end-compile-instance]] reaches W. (2) Acc is not even stateable at the surface, since Acc.intro's field is a function, so item 3 of [[stress-proof-suite]] would be a kernel-level test of the synthesized-ih beta rule rather than frontend progress — worth doing as insurance on trusted code with no end-to-end consumer, but not next. (3) The real bottleneck is that TyKind is 'Nat | a = b | Named<args>' and ExprKind's only application form takes a NAME as head. Container fields, the trait layer, user-written optimization passes, Compile instances, and the whole mathematics side all sit behind function types. (4) Function types are a pure surface+elaborator round — Pi/Lam/App landed in kernel v0 — so unlike the last two rounds there is no trusted-base change and no ch. 07 obligation. Also noted for later: [[kernel-v1-extensions]] still claims inductive families come from indexed W, but the branching argument (beta on open children) applies verbatim, so indexed FINITARY families should ford over Wf — consistent with [[inductive-compiler]]'s own scope note that indices are 'the same machinery, not a fourth tier'. That contradiction should be resolved before a typed IR is designed.
- 2026-07-26: Item 8 [[surface-function-types]] LANDED and closed: dependent '(x: A) -> B' / 'A -> B', 'λ (x: A) => e' (with 'fun' as the ASCII synonym), postfix application so a call head is any expression, and lambda checking/inference against the kernel's Pi/Lam/App. 26 acceptance tests, workspace at 379. As predicted this needed no kernel change and no metatheory pass. The immediate payoff is cong over an ARBITRARY function, deferred since [[surface-operators]]. Next focus: item 9 [[nested-inductives-container-fields]], whose design fork (indexed accessor vs fold) this round was blocking — the fold is now an ordinary function taking a lambda, so no special-form eliminator is needed. Two things filed rather than folded in: [[implicit-binders-in-function-types]] (wanted on by-value functions, structurally blocked because implicitness lives in ParamMeta keyed by declaration name rather than in Type::Pi) and [[annotated-let-swallows-the-equals]] (pre-existing parser bug, found while probing hole-under-lambda).
