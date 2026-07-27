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
8. ✅ [[surface-function-types]] — dependent `->` and `λ`; the surface type
   grammar is three constructors wide and this is what widens it. No kernel
   change (Π/λ/App are v0), so no metatheory round.
9. ✅ [[nested-inductives-container-fields]] — container field types (`Rose`),
   phases 1–3 landed: it declares, computes and proves. What any IR needs
   and what finite sequences need on the
   mathematics side. The issue stays open for the phases beyond `Rose`.
10. ✅ Tier 2 / `Acc` by hand ([[stress-proof-suite]] item 3) — a kernel-level
    test of the synthesized-ih β rule, not frontend progress, since `Acc` is
    not stateable at the surface (function-typed field). docs/acc-via-w.md.

Rounds 1–10 are done. [[stress-proof-suite]] said passing the suite would
unlock [[ir-simulate-design]] in-language; **that is deliberately not next**
(see "Round two" below and the 2026-07-26 log entry).

## Round two: language features, not elaborator features

The organizing principle, agreed 2026-07-26: **fewer special features in the
elaborator, more fundamental features in the language.** Round one bought a
usable surface, but several of its capabilities are elaborator machinery
wearing a syntax — generics are a substitution table consulted while lowering
one declaration, `Vec` is a built-in type former with no eliminator, motives
have their own binder syntax, implicitness is a side table keyed by
declaration name. Each of those is a thing the language could simply *have*.
The IR sits behind them, not the other way round: a typed IR written against
magic inherits the magic.

11. ~~**[[surface-polymorphism]] + [[implicit-binders-in-function-types]]**,
    as one round.~~ **Done 2026-07-26** — but as *polymorphism only*.
    `fn map<A, B>(f: A -> B, xs: List<A>) -> List<B>` writes, checks and
    computes. [[implicit-binders-in-function-types]] did **not** have to come
    with it: a type parameter is a declaration parameter, so implicitness
    stayed exactly where it already was and no polymorphic call spells its
    type arguments. It stays open as ergonomics, for applying a polymorphic
    function *value*. No trusted-base change and no ch. 07 obligation, as
    predicted.
12. **[[surface-records]]** — named-field Σ sugar, then the trait layer
    ([[compile-typeclass-design]]) on top. An algebraic structure and a
    `Compile` instance are both records of generic functions, so this wants
    11 first.
13. **[[motives-as-lambdas]]** — small; `match … as x -> M` and
    `j(p, (y,q) -> M, case)` become ordinary λs, and `->` stops meaning two
    things. Sets up `j`/`refl`/`cong` becoming declarations rather than
    syntax once 11 lands.
14. **[[indexed-families]]** — retires built-in `TyKind::Vec`/`VecLit` in
    favour of a declared family, and resolves the standing
    indexed-`W`-vs-`Wf` contradiction the roadmap flagged as needing an
    answer *before* a typed IR is designed.
15. Then [[ir-simulate-design]] in-language, with [[datarepr-separation]] and
    [[end-to-end-compile-instance]] behind it.

Direction, not scheduled: [[generators-in-the-language]] — the derived
artifacts (recursors, no-confusion, the tier lowerings) are Rust that emits
kernel terms, and the thesis says they belong in the meta layer. Wants 11 and
12 first, and an expressiveness reading of ch. 07 before it can be planned.

Cheap and separable, pick up any time: [[cli-check-diagnostics]] (there is
still no way to check a file outside a Rust test), the postponement slice of
[[elab-unifier-completeness]], [[annotated-let-swallows-the-equals]],
[[warn-bare-eq-no-effect]].

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
- 2026-07-26: Item 8 [[surface-function-types]] LANDED and closed: dependent '(x: A) -> B' / 'A -> B', 'λ (x: A) => e' (with 'fun' as the ASCII synonym), postfix application so a call head is any expression, and lambda checking/inference against the kernel's Pi/Lam/App. 26 acceptance tests, workspace at 379. As predicted this needed no kernel change and no metatheory pass. The immediate payoff is cong over an ARBITRARY function, deferred since [[surface-operators]] — though see the correction: the deferred SPELLING '.cong(Succ)' still needs a lambda, because constructors are saturated-only ([[constructors-as-function-values]]). Next focus: item 9 [[nested-inductives-container-fields]], whose design fork (indexed accessor vs fold) this round was blocking — the fold is now an ordinary function taking a lambda, so no special-form eliminator is needed. Two things filed rather than folded in: [[implicit-binders-in-function-types]] (wanted on by-value functions, structurally blocked because implicitness lives in ParamMeta keyed by declaration name rather than in Type::Pi) and [[annotated-let-swallows-the-equals]] (pre-existing parser bug, found while probing hole-under-lambda).
- 2026-07-26: Side round, off the focus order: [[constructors-as-function-values]] LANDED and closed (docs/constructor-function-values.md, crates/elab/tests/constructor_values.rs, 9 tests, workspace at 412). 'twice(Succ, 0)', 'ap(Wrap, 1)', 'Cons(1)' and 'Node(0, 1)' at a container type all elaborate, so a constructor is a function value wherever something is checking it. Two independent halves, worth keeping distinct: 'Succ' became an ordinary resolvable NAME (a lambda at Pi(Nat).Nat, no expected type needed) — that is the half that discharges [[surface-operators]]' '.cong(Succ)', because cong's implicit endpoints put its argument in an INFERENCE position that the other half cannot reach — and declared constructors eta-expand against the expected Pi in checking position. Nothing tier-aware was needed. Correction to the filed plan, docs §5.1: 'Cons(1)(xs)' also reaches inference (its head is an application, not a name) and is fixed by re-associating the constructor spine, not by building a field telescope; so the boundary is 'an unsaturated constructor needs a checking position only if it STAYS unsaturated'. Still open by choice: a bare unsaturated constructor in inference position ('let f = Wrap;', '.cong(Wrap)') — inferring its type is a second copy of the lowering's field layout and is impossible for a parameterized declaration; the '.cong(Wrap)' half is [[elab-unifier-completeness]]' (apply_implicit infers where it could check). Focus order unchanged: item 9 [[nested-inductives-container-fields]] phase 3, then item 10 Acc.
- 2026-07-26: Item 9 [[nested-inductives-container-fields]] phase 3 DESIGNED (docs/container-proofs.md); implementation is the next code round. It needs no kernel change and no metatheory pass — one elim_Nat schema and a typing rule — so it stays a pure surface+elaborator round like item 8. Recorded there because it revises a standing assumption: an 'All' predicate over a vector is definable in this kernel (codes + El give large elimination at Prog layer), so the reason the design does not use it is that the SURFACE cannot eliminate a vector, which puts 'All' behind the deferred Fin/indexing layer rather than behind any kernel work. Focus order otherwise unchanged: phase 3 code, then item 10 Acc.
- 2026-07-26: Item 9 [[nested-inductives-container-fields]] phase 3 LANDED (docs/container-proofs.md, crates/elab/tests/container_proofs.rs, workspace at 421): 'size(r) = size_plus(r)' over Rose is the first theorem here proved by induction over a container. One new elim_Nat schema (tab_cong) and one typing rule; no kernel change and no metatheory pass, as predicted. Container fields are now complete through the phases that were scoped: Rose declares, computes, and proves. Two live shift bugs fell out, one of them phase 2's and invisible to every test it shipped with, both recorded in docs/container-proofs.md §10. Next focus: item 10 — tier 2 / Acc by hand ([[stress-proof-suite]] item 3), the synthesized-ih beta rule; then [[ir-simulate-design]] reopens in-language. Note for whoever picks up Acc: the ih-annotation class of bug found this round (an annotation only compared when a PROOF forces it, never when a closed value computes) is exactly what a kernel-level Acc test is insurance against.
- 2026-07-26: Item 10 (tier 2 / Acc by hand) DONE, closing [[stress-proof-suite]] -- docs/acc-via-w.md, crates/kernel/tests/acc.rs, 13 tests, workspace at 434. It did what the item was insurance for: elim_W's synthesized-under-a-lambda ih fires at an abstract position, with the recursor equation wfrec(a; intro(a;h)) == st a (lam b r. wfrec(b; h b r)) holding DEFINITIONALLY at open a, h and st, plus closed computation through a node of infinite arity and three negative controls (mis-indexed children rejected, wrong values inconvertible, stuck at a variable accessibility proof). The ih-annotation hazard the previous round flagged for whoever picked this up did NOT recur -- the analogous hazard here is the ih SPINE (position argument first), and it fails loudly rather than silently. Two standing claims corrected, both logged on their own issues: tier 2 needs no funext for the recursion direction ([[kernel-v1-extensions]]), and [[empty-eta-conversion]] has lost the customer it was filed with. All ten roadmap items are now done; next focus is [[ir-simulate-design]] reopening in-language, which the suite's own acceptance clause pointed at.
- 2026-07-26: Round two set, and the IR deliberately deprioritized. The suite's closing line has been pointing at [[ir-simulate-design]] for three rounds; on review it is not the Next Immediate Thing, because several round-one capabilities are elaborator machinery wearing a syntax and a typed IR written against them would inherit them. Organizing principle for round two, in the user's words: fewer Special Features in the elaborator, more fundamental features in the language. New order: 11 [[surface-polymorphism]] + [[implicit-binders-in-function-types]] together (you cannot write 'fn map<A,B>' -- Decl has no type parameters at all, and an inductive's parameters are MONOMORPHIZED so List<A> is a macro, not a type-level function; the kernel has had Pi(A : Ty 0) + El since v0, so it is a pure surface+elaborator round like function types); 12 [[surface-records]] then the trait layer; 13 [[motives-as-lambdas]] (small; also un-overloads '->'); 14 [[indexed-families]] (retires built-in TyKind::Vec/VecLit and settles the indexed-W-vs-Wf contradiction this issue flagged as needing an answer before a typed IR is designed); 15 the IR. Filed as direction rather than scheduled: [[generators-in-the-language]] -- the recursors, no-confusion and tier lowerings are Rust emitting kernel terms, and the thesis says they belong in the meta layer; wants 11 and 12 plus an expressiveness read of ch. 07 first. Not filed as new work, because they already have issues: the cheap separable items (cli-check-diagnostics, unifier postponement, the two parser/diagnostic bugs).
- 2026-07-26: Item 11 done: [[surface-polymorphism]] landed (docs/surface-polymorphism.md, 33 tests, workspace 465). Two corrections to the order's reasoning. (a) It was filed as one round with [[implicit-binders-in-function-types]]; that turned out to be unnecessary, since a type parameter is a declaration parameter and implicitness already lives there -- that issue stays open as ergonomics, for applying a polymorphic function value. (b) The round cost nothing in the tier-0/1 generators: an inductive's parameters stay expanded per instantiation, and an OPEN instantiation is all 'map' needed to return a List<B>. Next per this order: 12 [[surface-records]].
