---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-07-31
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
12. ✅ **[[surface-records]]** — named-field Σ sugar, landed 2026-07-27
    (`docs/surface-records.md`, 33 tests). Next on this line is the trait layer
    ([[compile-typeclass-design]]) on top. An algebraic structure and a
    `Compile` instance are both records of generic functions, so this wants
    11 first.
13. ✅ **[[surface-universe]]** — the Type Session, landed 2026-07-27 in five
    phases, with [[motives-as-lambdas]] as phase 3 (closed). `Type<n>` is
    writable, so a level join is no longer vacuous. Residue has its own homes:
    [[implicit-level-polymorphism]] and [[special-forms-as-declarations]].
14. **[[indexed-families]]** — a surface form for declaring an indexed
    family, and the resolution of the standing indexed-`W`-vs-`Wf`
    contradiction this issue flagged as needing an answer *before* a typed IR
    is designed. It does **not** retire `TyKind::Vec`/`VecLit`; that was this
    order's own claim and it is withdrawn (2026-07-27) — see that issue's
    scope notes for why the container has to stay primitive.
    **Resolution direction agreed 2026-07-28** (the contradiction is answered
    for sequencing purposes): a classification. The index-recursive fragment
    (that issue's route 1, `Nat` *and* inductive indices) is this item and
    unblocks 15–16; the general case fords over an irrelevant equality and
    waits on **[[sprop-strict-prop]]**, a kernel round scheduled off-order.
    It does not gate 15–16: [[ir-simulate-design]] specifies an ordinary
    inductive with fuel, and if the IR wants typing intrinsically that is a
    decision that issue has not made (an extrinsic well-typedness predicate
    is route 1). The indexed former (route 4) stays the measured fallback,
    to be prototyped against 2b once SProp lands.
15. **[[cli-check-diagnostics]]** — promoted from "cheap and separable"
    (2026-07-27): the IR round is the first that writes substantial Heather
    files rather than test snippets, and checking them only through a Rust
    test harness is friction on exactly that round. Also the harness
    [[frontend-benchmarks]] assumes.
16. Then [[ir-simulate-design]] in-language, with [[datarepr-separation]] and
    [[end-to-end-compile-instance]] behind it.

Direction, not scheduled: [[generators-in-the-language]] — the derived
artifacts (recursors, no-confusion, the tier lowerings) are Rust that emits
kernel terms, and the thesis says they belong in the meta layer. Wants 11 and
12 first. Its ch. 07 expressiveness reading (can the meta layer express the
tier-1 lowering as it stands?) **is** scheduled, as an unordered side round —
a reading exercise, and if the answer is "missing kernel features," that is a
metatheory round to know about before the IR stack sits on top.

Cheap and separable, pick up any time: the postponement slice of
[[elab-unifier-completeness]], [[annotated-let-swallows-the-equals]],
[[warn-bare-eq-no-effect]], [[split-on-arms]], [[named-arguments]],
[[j-binder-parse-trap]], [[prelude-option-and-friends]] (layer 1, the
prelude residency), [[nested-match-patterns]], and [[frontend-benchmarks]]
(design round; its harness assumption now holds via item 15).

Blocked on layers not yet built, listed so they are reachable rather than
only `ls`-able: [[implicit-level-polymorphism]] (wants level inference *and*
[[generators-in-the-language]]), [[special-forms-as-declarations]] (bounded to
level 0 until `UPi`, i.e. layer m).

Later, tracked where linked: implicit quotation + modal surface
([[surface-syntax]] round 2), context-specific compilation / certified PE
([[compile-typeclass-design]], [[certifying-generator]] — sketch round 3),
goal-solver meta-functions (sketch round 3 §2).


## Log

**Convention (from 2026-07-27):** an entry here is *one line* — what moved in
the focus order, and a link. The narrative of a round belongs to the issue
that owns it and to that round's doc; this log said it a second time, in
2026-07-27 to the tune of 3,400 words, and the second copy is what drifts.
Order *decisions* are the exception: sequencing is what this issue owns, so
those keep their reasoning. Entries before 2026-07-27 were compressed on that
date; the originals are in `git log --follow issues/frontend-roadmap.md`.

- 2026-07-23: Opened after stage 1 landed, alongside the granular issue split.
- 2026-07-24: Item 3 done — [[elab-stage2-metas]]. Level-meta inference
  deferred to [[elab-unifier-completeness]] and promoted to a jumpable item.
- 2026-07-24: Item 4 done — [[surface-operators]].
- 2026-07-24: Filed [[surface-proof-automation]], unscheduled.
- 2026-07-24: Equality notation settled — [[surface-syntax]]; follow-up
  diagnostic is [[warn-bare-eq-no-effect]].
- 2026-07-24: Item 5 done — [[match-recursion]].
- 2026-07-24: Item 2 done — [[metatheory-ch07-pass]]; tier 1 is no longer
  gated on unpaid metatheory debt.
- 2026-07-24: Item 6 done — [[goal-holes]]. Came with the block/`let` grammar,
  which unblocks [[surface-proof-automation]]'s cheap slice.
- 2026-07-24: Item 7 tier 0 done — [[inductive-compiler]].
- 2026-07-26: Item 7 remainder done on the linear side; [[stress-proof-suite]]
  item 2 closed.
- 2026-07-26: **Order change.** Items 8–10 were "tier 2 / Acc, then the IR";
  now [[surface-function-types]] → [[nested-inductives-container-fields]] →
  Acc. Reasoning, which is this issue's own: (1) Acc is not on the critical
  path — [[ir-simulate-design]] specifies a *fuel-indexed* simulate, so it
  recurses on `Nat` and nothing before [[end-to-end-compile-instance]]
  reaches `W`; (2) Acc is not stateable at the surface at all, so it is a
  kernel-level test rather than frontend progress; (3) the real bottleneck is
  that `TyKind` is `Nat | a = b | Named<args>`, and container fields, traits,
  user-written passes and the mathematics side all sit behind function types;
  (4) function types need no kernel change, so no ch. 07 obligation. Also
  flagged here and now resolved on [[indexed-families]]: the standing
  indexed-`W` claim in [[kernel-v1-extensions]].
- 2026-07-26: Item 8 done — [[surface-function-types]]. Filed:
  [[implicit-binders-in-function-types]], [[annotated-let-swallows-the-equals]].
- 2026-07-26: Side round — [[constructors-as-function-values]] done.
- 2026-07-26: Item 9 done, phases 1–3 —
  [[nested-inductives-container-fields]].
- 2026-07-26: Item 10 done — Acc by hand, closing [[stress-proof-suite]].
  Corrected two standing claims, each logged on its own issue
  ([[kernel-v1-extensions]], [[empty-eta-conversion]]).
- 2026-07-26: **Order change — round two set, IR deliberately deprioritized.**
  The suite's closing line had pointed at [[ir-simulate-design]] for three
  rounds; on review several round-one capabilities are elaborator machinery
  wearing a syntax, and a typed IR written against them inherits them.
  Organizing principle, in the user's words: *fewer special features in the
  elaborator, more fundamental features in the language.* New order: 11
  [[surface-polymorphism]], 12 [[surface-records]], 13 [[motives-as-lambdas]],
  14 [[indexed-families]], 15 the IR. [[generators-in-the-language]] filed as
  direction, not scheduled.
- 2026-07-26: Item 11 done — [[surface-polymorphism]]. It did *not* need
  [[implicit-binders-in-function-types]] as filed; that stays open as
  ergonomics for applying a polymorphic function value.
- 2026-07-27: Item 12 done — [[surface-records]]. Filed:
  [[numeral-stack-depth]].
- 2026-07-27: Side round — [[method-receiver-position]] done. Leaves
  [[named-arguments]] as the last "stop deciding this by position" item.
- 2026-07-27: **Order change.** Item 13 is gated on a missing form, so the
  round became [[surface-universe]] — the Type Session — with
  [[motives-as-lambdas]] as its phase 3. The same sentence had been written
  four times across four rounds: `TyKind` cannot say `Type`, so every writable
  type joins to 0 and every level join is vacuous. Universe polymorphism
  stayed out and its route around is now known, which promotes
  [[generators-in-the-language]] from direction to the only route to a
  level-generic library.
- 2026-07-27: Items 12 and 13 closed — [[surface-universe]] complete through
  phase 5, closing [[motives-as-lambdas]]. Residue re-homed rather than left
  in a log: [[implicit-level-polymorphism]] and
  [[special-forms-as-declarations]]. Item 14 [[indexed-families]] is next,
  then 15 [[ir-simulate-design]].
- 2026-07-27: Item 14 rescoped, and this log compressed. [[indexed-families]]
  was rewritten: its acceptance criterion (retire `TyKind::Vec`/`VecLit`) is
  **withdrawn as wrong**, not deferred, so item 14's description here changed
  with it. The rewrite's occasion is the organizational point above — that
  issue restated facts owned by [[nested-inductives-container-fields]] and
  went stale within a day of filing — which is also why `scripts/issue` now
  prints backlinks on `show`/`close`/`log`.
- 2026-07-27: **Order change.** [[cli-check-diagnostics]] promoted to item 15,
  between [[indexed-families]] and the IR. Reasoning, which is this issue's
  own: the IR round writes real Heather files, and there is still no way to
  check one outside a Rust test; a check loop should predate the round that
  needs it, and [[frontend-benchmarks]]'s harness is "time the CLI on the
  corpus."
- 2026-07-27: Filed [[kernel-benchmarks]] and [[frontend-benchmarks]] —
  evaluation cost is load-bearing (kerneltime execution, equiv-by-conversion)
  and nothing measures it. Scheduled [[generators-in-the-language]]'s ch. 07
  expressiveness reading as an unordered side round.
- 2026-07-28: Order decision: SProp promoted from foundations-later to a scheduled kernel round — [[sprop-strict-prop]] filed; item 14 resolves as route 1 now plus SProp-then-2b for the general case, neither gating items 15-16.
- 2026-07-30: Item 14's route-1 fragment landed — indexed families declare, compute and prove (scheme doc docs/inductive-indexed-lowering.md, prototype + generator; narrative on [[indexed-families]]). The general (fording) case stays with [[sprop-strict-prop]]/[[indexed-families]]; 15 is unblocked.
- 2026-07-30: Item 15 done — [[cli-check-diagnostics]]. The goal listing has its face; [[frontend-benchmarks]]'s harness assumption now holds. Next: 16, [[ir-simulate-design]].
- 2026-07-30: Side round off item 14: doc §8.2's instantiation claim is now measured — declared-index hand prototype green ([[indexed-families]] 2026-07-30). The IR round (16) can state extrinsic judgments over declared syntax in route 1's fragment; the declared-index generator stays on [[indexed-families]].
- 2026-07-31: Item 16 opened -- [[ir-simulate-design]]'s design sketch landed (docs/ir-simulate-design.md); the implementing round follows the doc's section 11 acceptance list.
- 2026-07-31: Item 16 part 1 landed -- [[ir-simulate-design]] section 11 items 1/2/6 in lib/ir_v1.hthr; [[simulate-conversion-cost]] filed off it (conversion-time evaluation is the new critical-path performance issue); items 3-4 (the converges interface and its proofs) are the round's continuation.
