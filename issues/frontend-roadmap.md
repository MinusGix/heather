---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-09-13
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
    unblocks 15–16; the general case fords over an irrelevant equality —
    the SProp kernel round landed and closed ([[sprop-strict-prop]],
    2026-08-02; metatheory residue at [[metatheory-ch07-sprop]]), so the
    2b generator waits only on its own round at [[indexed-families]].
    It does not gate 15–16: [[ir-simulate-design]] specifies an ordinary
    inductive with fuel, and if the IR wants typing intrinsically that is a
    decision that issue has not made (an extrinsic well-typedness predicate
    is route 1). The indexed former (route 4) lost the prototype comparison
    (2b passed the setoid bar 2026-07-29, zero new kernel machinery) and
    stays the unexercised fallback.
15. ✅ **[[cli-check-diagnostics]]** — landed 2026-07-30 (`heather check`,
    snippets, per-declaration recovery). Was promoted from "cheap and
    separable"
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

Also direction, not scheduled: [[parallel-checking-and-caching]] — many
concurrent sessions over one shared telescope, a content-addressed
declaration cache, and the quickcheck/check/build split; certificate replay
is the agreed trust direction. Its spine starts at
[[elaboration-determinism]] and pays off single-session from the first
stage.

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
- 2026-07-31: Side round off item 16: the simulate bench fixtures land (kernel suite) and the delam definitions reading is done -- verdict on [[simulate-conversion-cost]]: [[subst-visits-closed-subtrees]] first (implementation-only, fixture-gated), the definitions extension second (new-former-grade, layer-indexed transparency as its charter).
- 2026-07-31: The subst round from that sequencing landed and closed same-day ([[subst-visits-closed-subtrees]]): simulate-payload slope 0.00, ir_v1 release check 107s -> 13.6s; the definitions round is next in line.
- 2026-07-31: Item 16's blocking performance issue is closed: [[simulate-conversion-cost]] landed kernel definitions with layer-indexed transparency and the elaborator switch from fn-inlining to Psi-references; lib/ir_v1.hthr's full acceptance is back under scripts/test.
- 2026-08-01: 2026-08-01: Item 16 done — [[ir-simulate-design]] closed, §11 fully discharged and re-verified (elab test green, release check 33.7s); residue re-homed to [[cross-ir-refinement]]. [[compile-typeclass-design]] and [[end-to-end-compile-instance]] unblock; the Compile design round opens.
- 2026-08-01: 2026-08-01: The Compile round opened AND its milestone landed same-day — [[compile-typeclass-design]]'s design sketch (docs/compile-typeclass-design.md: instance = ordinary record value; class layer deferred to the resolver round with prerequisites recorded) plus its §7 acceptance in lib/ir_v1.hthr, closing [[end-to-end-compile-instance]]. The thesis milestone is checked: hand-written Compile instance for add, kernel-verified certificate, no generator. Behind it per the old item 16 note: [[datarepr-separation]] and [[certifying-generator]].
- 2026-08-01: The certifying-generator round opened with its design sketch (docs/certifying-generator-design.md) — v1 is a Rust surface-text transpiler reproducing the hand-run add section schematically; the implementing round follows the doc's section 9 acceptance list.
- 2026-08-02: The generators-in-the-language ch. 07 expressiveness side round is done — verdict on that issue: missing features, enumerable (opaque globals, no oracle, no code equality, no context computation); the vec.rs schemas and the certifying generator's v1 fragment are the expressible frontier, so the Rust transpiler prototypes the in-language generator's natural first scope.
- 2026-08-02: The certifying-generator v1 landed (crates/elab/src/certgen.rs): generated Compile instances with kernel-checked certificates for add, dbl, seven, third3 — the first machine-written certificates in the repo; narrative and the bound-spelling correction on that issue.
- 2026-08-02: Certifying-generator v2 landed same-session: the existential-composition kit in lib/ir_v1.hthr (four lemmas, proved once) plus the generator rewritten to fold it — mul-via-add is the first machine-written CROSS-FUNCTION certificate, the callee's invariant consumed at an open argument. Filed: [[prog-extension-lemma]], [[in-language-map]], [[certgen-harness-cost]].
- 2026-08-02: The in-language-map round opened AND landed same-session (docs/in-language-map-design.md): the quotation slice (meta fn / code blocks / $-splices / let code), the elaborator-held evaluation hook, and lib/vec_code.hthr's map_code — the first in-language derived artifact, cross-checked against Rust vec::map up to conversion. Two calculus findings recorded on [[in-language-map]]: code arguments cannot index types (no meta-functions over terms), and layer-p types cannot appear inside code — so generic templates bind their types inside the quote, and TyCode binders wait for the analysis story. Next per the migration order: the certifying generator's fragment transcriber.
- 2026-08-02: 2026-08-02: the let/blocks cluster landed (docs/let-and-blocks-design.md). [[annotated-let-swallows-the-equals]], [[match-arm-blocks]] and [[j-binder-parse-trap]] closed in one round -- an annotated `let` at every type, a prefix-`{` block expression, and three rules over the six keyword-headed atoms. One residue filed with an owner: [[let-inside-quotation]], whether a block may be a `code { … }` payload (declined for now at both the parser and scan_splices).
- 2026-08-02: [[sprop-strict-prop]] closed complete (kernel round + 2b acceptance); residue rehomed to [[metatheory-ch07-sprop]] (FT pass) and [[sprop-squash]] (deferred formers, unscheduled). Item 14's general case now waits only on the 2b generator round at [[indexed-families]]; body updated.
- 2026-08-03: [[indexed-families]] §8.2 generator landed (managed round): declared index types — enum, linear Wf, and branching derivation-shaped families — are declarable at the surface; subject-recursive judgments are now shipped, not just prototyped. Remaining on item 14: the 2b generator (general case), multi-index, indexed absurd/inj.
- 2026-08-03: Item 14's general case moved: route 2b's scheme doc (docs/inductive-fording-lowering.md) and Wf-composition prototype landed, closing the scheme's one untested corner and correcting the 2026-07-29 beta finding (proof-keyed, not open-data-keyed) — narrative on [[indexed-families]]. The 2b generator (doc sec 13.2) is its own next round; multi-index and indexed absurd/inj remain behind it.
- 2026-08-04: Item 14's general case SHIPPED: the 2b generator landed (managed round; narrative on [[indexed-families]]). Computed-index, deep-pattern and non-uniform declarations now declare, match and prove at the surface; suite 891 → 908. The round also fixed a pre-existing case-tree annotation bug in wf.rs/indexed.rs (three-constructors-plus-open-payload blind spot; testing doc gains axis 6) and sharpened doc §8.4 (all-form-B declarations admit no induction over open data). Remaining on item 14: multi-index, indexed absurd/inj — both explicitly behind demand, not scheduled.
- 2026-08-04: Item 14 follow-on (managed round, narrative on [[indexed-families]]): form A at a declared index landed plus the inference rider — declared-index forded families now support closing induction at invertible constructors, and constructors infer their type arguments from a child argument or take a written instantiation. Suite 908 → 924. A classifier bug fixed on the way (nullary index constructors read as bare variables). Remaining on item 14 unchanged in kind: multi-index, indexed absurd/inj, plus two new measured boundaries (payload-argument index constructors stay form B; branching form A at a ≥3-constructor index exceeds the conversion fuel budget pending the kernel-def cut).
- 2026-08-04: The frontend benchmark suite landed (managed round, phase 1 of the kernel-def effort; narrative on [[frontend-benchmarks]]): nine families, phase-split corpus timing, exponent bands, baseline gated by scripts/bench-frontend --check; suite 924 → 929. Headline measurement: ir_v1.hthr is 98.8% kernel gate (elaborator optimization would aim at 1% of the heavy file), and the forded fixtures record slopes 3.39 / 2.65 as the defect phase 2 fixes. [[generated-term-defs]] filed as phase 2's owner — generator artifacts become named kernel definitions, measured against this baseline.
- 2026-08-04: Phase 2 landed same-day and [[generated-term-defs]] closed: generator terms are Ψ definitions, forded constants down 4–7× (computed-arms @6: 1.25s → 195ms; per-use 119 → 28ms), the §14.9 fuel-cliff negative flipped positive, suite 931. The instructive miss: the bands stayed green — residual superlinearity is the emitted TYPES, which cannot be Ψ definitions at all (no body on GlobalBinding::Ty); [[family-types-as-code-defs]] filed as the successor and it is also route 1's §10.3 lever. Perf accounting for the session: this was the deliberate round, and it closed two recorded seams with a measured number.
- 2026-08-05: The deliberate round: [[family-types-as-code-defs]] designed and landed same-day, closed — skeleton and index types are code definitions consumed as El-of-reference (docs/family-type-code-defs-design.md; kernel untouched, as the design verified against ch. 06). computed-arms slope 2.79 → 2.54, per-use 28 → 19 ms; declared-index-tags did NOT move (2.61 → 2.62) and the residual is a named third defect, [[wf-shape-annotation-slots]]. Route 1's successor round is specced on [[indexed-families]] (design §6). Perf accounting: this was the session's deliberate round.
- 2026-08-05: Side round, user-directed: [[modules]] — filed, designed
  (docs/modules-design.md) and landed v1 same-day, closing same-day;
  [[prelude-option-and-friends]] layer 1 satisfied by it. The certgen
  fragment transcriber was considered and deliberately deferred in its
  favor (user call: core-language and proving surface before more
  meta-layer migration). Suite 936 → 971.
- 2026-08-05: Side round, from the cheap list: [[match-with-equation]] and [[split-on-arms]] landed and closed in one round (docs/match-equation-split-design.md) — the equation binding `match h : e` and the `split`/`on` statement, plus a live tier-0 case_tree shift fix whose sweep is [[dependent-motive-crossing-sweep]]. Suite 1035 → 1059.
- 2026-08-05: Side round: [[dependent-motive-crossing-sweep]] done and closed — all five case-tree emitters' shifts audited correct and pinned by mutation-verified controls; the controls uncovered and fixed a forded-lowering defect (parameterized family over a non-recursive skeleton, narrative on [[indexed-families]]). Filed: [[type-arg-inference-through-index]], [[suite-wall-time-two-tests]]. Suite 1059 → 1064.
- 2026-08-05: Small round, direct: [[type-arg-inference-through-index]] fixed and closed — the walker learns type arguments through `elimN`-of-codes family types; the recorded hypothesis (reference opacity) was wrong and the correction is on the issue. Suite 1064 → 1067.
- 2026-08-05: Small round, direct: [[suite-wall-time-two-tests]] measured, corrected (the 13/15-min figures were loaded-machine wall-clock; the real cost is 120+160 CPU-s) and closed with scripts/test --fast (skips the two by name; inner loop 27.5s wall, default stays full). Growth watch stays with [[certgen-harness-cost]].
- 2026-08-05: From the cheap list, managed round: [[nested-match-patterns]] landed and closed (docs/nested-match-patterns-design.md) — pattern-matrix deep patterns plus the `_` arm with a shared-body rule, the three ir_v1 towers rewritten as decision trees, suite 1067 → 1093. Residue filed with owners: [[match-arm-redundancy-warning]], [[diagnostics-name-the-written-form]].
- 2026-08-07: 2026-08-07: Traits design discussion (user-led): docs/traits-design.md recorded in full and [[traits]] filed as owner — classes as parameterized records, canonical-value inheritance, disciplined resolution, := infer, programmable layer 3. Supersedes [[compile-typeclass-design]] §5. Implementing rounds per that doc's §13, first slice unscheduled as of this entry.
- 2026-08-07: Traits layer 1 landed 2026-08-07: `class`/`instance` declaration forms over records, block namespaces, `extends` with the canonical-value discipline ([[traits]], docs/traits-layer1-design.md). No resolver — that is layer 2.
- 2026-08-07: Traits layer 2 landed: the instance resolver and `:= infer` as one solver-parameter mechanism, with trace-as-data failures ([[traits]], docs/traits-layer2-design.md). Modes (out-params) are the one cut, with evidence; layer 3 still waits on context computation.
- 2026-08-07: 2026-08-07: Traits receiver dispatch landed: x.op(y) reaches a class member by building the goal C<typeof(x)> from the receiver's own kernel type and handing it to layer 2's resolver, then projecting ([[traits]], docs/traits-receiver-dispatch-design.md) — one route for concrete, generic and derivable carriers, and every ambiguity (ordinary member, bare name, builtin, second class) is an error naming both rather than a pick. Suite 1231 -> 1248.
- 2026-08-07: 2026-08-07: traits adopted by the library — lib/std/algebra.hthr declares the first classes (Monoid/Default/Cmp, an AddSemigroup→AddCommMonoid chain) and the instances lib/std's carriers earn; two findings with owners ([[inherited-members-undispatchable]], [[class-lemma-instantiation-fuel]]) and the ergonomics recorded on [[traits]].
- 2026-08-07: Typeclass constraints got their surface: `<A: Monoid>` inline with `+` stacking, one parser desugaring onto the existing solver parameter, both spellings coexisting in lib/std/algebra.hthr (issues/requires-placement-syntax.md). The three unobtrusiveness features round 2 recommended alongside it — type-level dot projection `A.unit`, `given` section variables, constraint bundles — are all still open, and dot projection is the one that unblocks migrating the remaining four library signatures off `requires`.
- 2026-08-07: 2026-08-07: Session close — agreed next-round order for the traits line (sequencing decision, this issue's own): owner-keyed dispatch + scope upcast ([[inherited-members-undispatchable]]) -> type-level dot projection ([[requires-placement-syntax]] round 2 candidate 23) -> [[operation-indexed-classes]] design pass -> operators-onto-classes. requires-removal intent recorded on [[requires-placement-syntax]] behind dot projection.
- 2026-08-08: The traits-line order's first round landed: owner-keyed dispatch + scope upcast ([[inherited-members-undispatchable]] closed, docs/traits-owner-dispatch-design.md; suite 1295 -> 1299). Next per the 2026-08-07 order: type-level dot projection ([[requires-placement-syntax]] candidate 23), now unblocked.
- 2026-08-08: The traits-line order's second round landed: type-level dot projection ([[requires-placement-syntax]] candidate 23; docs/traits-type-projection-design.md; suite 1299 -> 1326; five of six constrained library declarations anonymous). Filed off it: [[upcast-assembly-cost-at-open-carriers]] (0.7 s -> 25 s on plus_zero_of_comm, and a new entry on the requires-removal ledger). Next per the order: the [[operation-indexed-classes]] design pass, then operators-onto-classes.
- 2026-08-08: Perf interlude on the traits line, both rounds today: diagnosis then fix of [[upcast-assembly-cost-at-open-carriers]] (closed) — dispatched projections read through the upcast, plus_zero_of_comm anonymous at 0.948 s vs 35.9 s, suite 1326 -> 1328; docs/traits-named-upcast-design.md records the built-and-withdrawn Ψ-mint alternative. Perf accounting: this was the session's deliberate perf round. The order resumes at the [[operation-indexed-classes]] design pass.
- 2026-08-09: The traits-line order's third entry is done as a design pass: [[operation-indexed-classes]] designed with the user (docs/operation-indexed-classes-design.md) — indexed classes as the only law-bearing form, no bundled companion and no default instances, value slots filled by unification/scope/named-designation or refused. Implementing round one per doc §13 is next on this line; the operators round consumes doc §7 (designations, Monoid(+)).
- 2026-08-09: The traits-line order's third entry is fully paid: [[operation-indexed-classes]] round one landed (managed round; docs/operation-indexed-classes-design.md §14 for what implementing corrected; suite 1328 -> 1354; algebra.hthr 1.83s -> 0.42s, the additive hierarchy deleted). Filed off it: [[indexed-goal-derived-sharing]]. Next per the standing order: operators-onto-classes, consuming the design's §7 designation interface.
- 2026-08-09: The traits-line standing order (2026-08-07) is COMPLETE: operators-onto-classes landed as its final entry (design + implementation in one managed round, docs/operators-onto-classes-design.md; suite 1354 -> 1375; growth invariant pinned — no designation, same code). One table not two; the concrete-carrier terseness regression stands as a recorded decision. The traits line's remaining threads are demand-scheduled ([[operation-indexed-classes]] §8 diamond) or unscheduled ergonomics; the focus order returns to item 16's successors ([[datarepr-separation]], [[certifying-generator]]) or the cheap list.
- 2026-08-09: The roadmap itself stays open, as ever — it is the organizing issue.
- 2026-08-09: Small round, direct, from the cheap list: [[bool-operator-designations]] resolved and closed — `&&`/`||` as fixed tokens with designations at Bool, the semiring rows deleted, no fallback rung (docs/operators-onto-classes-design.md §13). Suite 1375 → 1383.
- 2026-08-10: The traits-adoption fuel finding is closed — [[class-lemma-instantiation-fuel]] identifies scoped type-closure reflexivity as the missing conversion shortcut and restores `concat_single<A>` to the library.
- 2026-08-11: The focus order's return to item 16's successors began at certifying-generator: the fragment transcriber is in-language (managed round; fifth-blocker finding, marker convention, analyzer slots — narrative on certifying-generator and generators-in-the-language). Suite 1439 -> 1448.
- 2026-08-11: 2026-08-11: The reflection line's cheap first step landed — in-language signature checking + the pull API's first cut (managed round; docs/fn-signature-reflection-design.md; narrative on [[fn-reflection-for-analyzers]]). The fragment definition now reads off lib/certgen_code.hthr whole; the opaque-globals kernel round now replaces an implementation, not an interface. Suite 1448 -> 1450.
- 2026-08-11: The generators line's first kernel blocker fell without a kernel round: [[opaque-globals-analysis]] filed, designed and landed same-day (managed round; docs/opaque-globals-analysis-design.md) — route A refuted from ch. 06's deliberate blocking, unfolding-for-analysis lands at the reflection boundary (fn_body_code + callee markers, zero kernel diff), mul-via-add transcribes in-language byte-identical to Rust v2. [[retire-rust-transcriber]] stage 2's gate is open (deletion is a user call). Blockers (2)-(3) stand. Suite 1450, count unchanged (coordinator correction: the agent's 1452 was fast-lane arithmetic; the round's checks land inside existing tests and the library file, and the full post-commit run says 1450 passed, 0 failed).
- 2026-08-12: The certgen line's fragment grows past Nat: non-Nat result embeddings landed (managed round, in-language only per the frozen-walker rule; narrative on [[certifying-generator]]). Suite 1474 -> 1476.
- 2026-08-15: Reality check (2026-08-15): item 16's tail advanced far while this list slept. datarepr v1 is complete end to end ([[datarepr-separation]]: both declaration forms, the Impl registry, reprgen with repr-typed results and callee-Impl resolution — arithmetic at Bin transfers, generated); and the impl declaration became a real surface ([[impl-declaration-surface]] closed; docs/obligation-records-design.md): inline clauses by AST splice, ? as a typed reporting hole, ':= derive()' as the first generator invocation ever requested from surface source, via_derived designed to degrade into a metafunction — a concrete step toward [[generators-in-the-language]]'s direction. The ergonomics thread ([[datarepr-surface-ergonomics]], closed) queued the follow-ons: [[repr-fold-via-abs-default]] (unblocked), [[idiomatic-spelling-pass]], [[repr-access-spellings]] (behind the now-raised [[theorem-field-projection-oom]]), [[proof-scale-abbreviations]], [[calc-equational-chains]], [[true-prop-trivial-hypotheses]], [[intrinsic-certification-style]].
- 2026-08-15: The queue-jumper is paid: [[theorem-field-projection-oom]] fixed and closed (managed round; named record projections in gendefs.rs, diagnosis on the issue) — a theorem-valued field now projects off an assembled record value, unblocking [[repr-access-spellings]]' dot-shaped reference form. Cost filed as [[record-projection-defs-declaration-cost]]. Suite 1579 -> 1590.
- 2026-08-15: From the datarepr ergonomics queue: [[repr-fold-via-abs-default]] landed and closed (managed round; narrative on the issue) — a repr's required clauses are R, abs and the mks, with fold defaulting to fold-through-abs whose anchor is DERIVED from the image laws (the round's finding: it cannot be refl), and the missing §3.3 transport-direction control is collected (UnC). Suite 1590 -> 1602.
- 2026-08-16: From the datarepr ergonomics queue: [[repr-access-spellings]] designed and landed (managed round; docs/repr-access-spellings-design.md, narrative on the issue) — every repr/impl access point is '<owner>::<member>' at the author's written name, minted names refused in user source with the designed form named, printed paths writable verbatim. Suite 1602 -> 1619. Next per the agreed order: the True mini-round ([[true-prop-trivial-hypotheses]]), then [[idiomatic-spelling-pass]] in one sweep.
- 2026-08-16: From the datarepr ergonomics queue: [[true-prop-trivial-hypotheses]] half 1 landed and the issue closed (managed round; narrative on the issue) — True is the kernel's Unit^0 claimed as a surface type name with bare 'trivial' as its inhabitant (no SProp decision needed: Unit eta is proof irrelevance), the defaulted inv retires the Zero = Zero pun, and rendered types print True at the display boundary. Half 2 re-homed at [[named-arguments]] as defaults-at-binders. Filed off it: [[datarepr-law-clause-inv-binders]]. Suite 1619 -> 1634. Next: [[idiomatic-spelling-pass]] in one sweep.
- 2026-08-16: The datarepr ergonomics queue is DRAINED: [[idiomatic-spelling-pass]] landed and closed (managed round; narrative on the issue) — datarepr/reprgen emissions, fixtures, hand-runs and doc examples all speak the idiomatic surface (n-ary application, unannotated multi-binder λ), naming untouched, mutation controls re-cut and hardened against parse-error false greens, semantics pinned by refl. certgen's three explicit-style sites deferred to [[certgen-emission-idiomatic-style]]. Suite 1634 -> 1635. Remaining queue items are design-shaped or demand-scheduled ([[proof-scale-abbreviations]], [[calc-equational-chains]], [[intrinsic-certification-style]], [[datarepr-law-clause-inv-binders]]); the focus order's next fork is the certifying-generator/meta-layer migration line vs a new design round — a user call.
- 2026-08-16: The fork is CALLED (user, 2026-08-16): the certifying-generator line resumes at the parameterized-instantiations round (datarepr's minted name feeding certgen's embed, docs/datarepr-design.md §1.4 gap 2), with [[certgen-emission-idiomatic-style]] riding its full-suite runs, and [[datarepr-law-clause-inv-binders]] paid first as the small companion.
- 2026-08-16: The companion is paid: [[datarepr-law-clause-inv-binders]] landed and closed (managed round; design and narrative on the issue) — a law clause mentioning one of its statement's own binder names free is elaborated under those binders (`Succ_abs := bin_succ_abs(a0)`), the whole-Π form unchanged and told apart syntactically, and the fixture's duplicated law is retired (BinNat and BinMin share one). Suite 1635 -> 1643. Next: the certgen × datarepr round.
- 2026-08-16: Small round from the certgen line: [[certgen-emission-idiomatic-style]] landed and closed — certgen's emissions speak the idiomatic surface (n-ary application, unannotated multi-binder λ), matching the datarepr family. A fourth site beyond the issue's three: the tier-1 ih, where the design doc had been describing the n-ary form all along while the emitter curried; the doc is now true. Also corrected on the way: docs/datarepr-design.md §5.1's "v1 is complete except for the repr-typed-result transfer" was stale by one day (that stage landed in d0e6af6, and parameterized instantiations landed with datarepr v1 itself) — both were briefly re-picked as "next" from that prose. Suite 1643, unchanged (a style flip plus a shared control guard, no new tests); scripts/bench --check: 18 comparisons within thresholds.
- 2026-08-17: The library push took over the focus order for a day and the roadmap did not follow it — recorded here late, in one entry. Two inference fixes landed off wave L1/L2's ranking ([[curried-tail-type-arg-inference]], [[match-arg-of-polymorphic-callee-needs-motive]]), then THREE rounds ran in parallel and merged the same day: waves L2′ + L3 ([[std-list-l2-prime-laws]], [[std-list-mem-and-perm]]), wave I ([[std-int-encoding]], closed), and the diagnostics pair ([[le-diagnostics-print-raw-el]], [[check-fallback-discards-expected-type]], both closed). Suite 1806 → 1836, verified by a full `scripts/test` on the merged tree rather than by summing the rounds' own runs. [[std-api-waves]] is now spent to its end and says so; its remaining rows are unowned residue and a long-range direction.
- 2026-08-17: **Order recommendation, this issue's own, from the three rounds above:** the next round is the motive pair — [[goal-motive-by-scrutinee-abstraction]] (10 sites) and [[nested-match-on-field-binder-motive]] (14 sites). Reasoning: they are two failure conditions of one function (`synth_motive` — a goal never put in whnf, and a scrutinee that is not a `Term::Var` because tier-0 field binders are projection aliases), each was ranked #1 by a round that could not see the other, and neither is localized by the diagnostics that landed beside them (verified post-merge on both issues). This is the first time in this push that two independent rounds ranked the same elaborator function first. Behind it, in the order the evidence supports: [[motive-application-hides-hypothesis-type]] (10 sites), [[instance-key-collides-across-modules]] (a traits-layer-2 design bug, not ergonomics — instance keys are the carrier head's SURFACE name, so `int::Le` collides with `nat::Le`), [[congruence-by-anti-unification]] (fourth consecutive round, 58 applications in `Int` alone, and §3 already has the algorithm).
- 2026-08-17: Filed off the diagnostics round, and it is the roadmap's business rather than a round's: `scripts/bench-frontend --check` is BROKEN AT HEAD ([[frontend-bench-ir-closure-stale]]) — a stale fixture whose imports no longer close, so the untruncated `ir_v1` case never runs and the suite's latency budget is unenforced; three slope bands also exit at HEAD, logged on [[frontend-benchmarks]]. `scripts/bench --check` (the kernel gate) is unaffected and green. Nobody noticed because the gate that would have said so is the broken one.
- 2026-08-17: The bench-harness round landed ([[frontend-bench-ir-closure-stale]] closed; bands re-recorded on [[frontend-benchmarks]]): the frontend corpus computes its import closure with the CLI's own loader instead of a hand-written list, its checksum counts Ψ bindings instead of errors, the heavy rows are re-recorded with dated proof the 17× drop is real optimization, and the slope bands are proven stale rather than noisy (six-run spread ≤ 0.07 against a documented ±0.25 that turned out to be a load-~10 figure). `ir_v1`'s 150 s latency budget is enforced again for the first time since the breakage, at 3.78 s.
- 2026-08-17: **Correction the roadmap owes its own earlier entries**, from that round: [[frontend-bench-baseline-host-string]] — both baselines record host `minus-pc` and this machine answers `minus-desktop`, so on a host mismatch the harness disables TIME comparisons, prints `ok` and exits 0. The frontend suite has been shape-only for weeks; the kernel suite still is, so today's four `scripts/bench --check` greens — cited in three round commits and the merge — are shape-only verdicts and not evidence that nothing got slower. The frontend baseline was re-recorded (that round's subject); the kernel baseline deliberately was not, and choosing between re-recording it and keying comparability on cpu+profile+rustc rather than hostname is a decision this roadmap should schedule rather than let the next round trip over. Also open from the same round: [[frontend-bench-heavy-contaminates-cheap-cases]] (the full `--check`'s time half flags cheap cases at 1.3–1.5× after the heavy corpus has run in-process, above its own 1.25× threshold — believe `--no-heavy` for times until fixed) and [[prelude-clone-cost-grew]].
- 2026-08-17: The scheduled bench-gate decision is TAKEN and paid (small direct round; narrative on [[frontend-bench-baseline-host-string]], closed): time comparability is keyed on cpu+profile+rustc in both harnesses (hostname never consulted), a skipped time half is a distinct `shape-only` verdict at exit 3 with compared/skipped counts, and the kernel baseline is re-recorded on this host with drift accounting (one finding routed to [[bounds-metadata-taxes-one-shot-checking]]). Both gates are full-comparison green again — `scripts/bench --check` ok 106, `scripts/bench-frontend --check --no-heavy` ok 50 — so a round's bench green means times again. The standing caveat remains [[frontend-bench-heavy-contaminates-cheap-cases]]: believe `--no-heavy` for frontend times. Next: the motive pair round per this date's order recommendation, dispatched managed.
- 2026-08-17: The motive pair round landed (managed round; docs/goal-motive-synthesis-design.md; narratives on [[goal-motive-by-scrutinee-abstraction]] and [[nested-match-on-field-binder-motive]], both closed): one function, TWO mechanisms — the one-defect hypothesis held for the site and not for the fix, so the issues stay two records (coordinator call, condition not met). 23 of the 24 charged library motives deleted; le_of_lt's is an inference-position convoy, not this defect. Suite 1836 → 1846 and `scripts/bench --check` ok 106, both verified on the merged tree under the just-restored full time gate. Residue with an owner: [[kernel-bench-full-run-flags-drift]] (the kernel twin of the frontend contamination signature). Next per the 2026-08-17 order: [[motive-application-hides-hypothesis-type]] (10 sites), then [[instance-key-collides-across-modules]] (design discussion first — traits-layer-2 design bug), then [[congruence-by-anti-unification]].
- 2026-08-17: The order's second entry landed (managed round; docs/argument-type-reduction-design.md; narrative on [[motive-application-hides-hypothesis-type]], closed): implicit filling reads an argument's type by whnf when the syntactic read learns nothing — the d180c1a principle extended to reducible types, at the read site so every consumer benefits. std/int loses all 22 @-spellings; the issue's 10-site count corrected to 8 by measurement (fourteen were consistency spelling, green on the old elaborator — correction propagated to [[congruence-by-anti-unification]]'s arithmetic). Composition with the same-day motive-synthesis round is a test. Residue with an owner: [[goal-context-entry-printed-in-the-wrong-context]] (hole context entries render against the whole of Γ, a pre-existing display defect). Suite 1846 → 1854 and bench ok 106, verified on the merged tree. Next per the order: [[instance-key-collides-across-modules]] (user-led design discussion first), then [[congruence-by-anti-unification]] — whose site count this round just changed; re-read before scheduling.
- 2026-08-17: The display residue is paid (managed round, run in parallel with the instance-identity round; narrative on [[goal-context-entry-printed-in-the-wrong-context]], closed): goal-hole context entries render against their own prefix of Γ via Cx::prefix, aliases at their binding depth by the use-sites' own invariant, and the sweep found no other whole-Γ display site in the tree. Suite 1854 → 1858, verified on the merged tree.
- 2026-08-18: The order's third entry landed (managed round after the user-led design discussion it asked for; docs/instance-resolved-key-design.md; narrative on [[instance-key-collides-across-modules]], closed): an instance's identity is resolved declaration references end to end — no surface spelling is load-bearing in the registry — with module qualification as the external face (nothing needed minting) and the lexer's `::` join lifted to a chain, retiring layer-1 §8's three-segment residue with its first paying customer. The win at all three carriers: the Int round's stalled Decide<Le> row lands, std/bool un-dodges Le_bool, nat and bool gain their `<=` designations. Residue with owners: [[designation-key-collides-across-modules]] (same latent key in the designation table, no failing customer yet) and the cost-shrink on [[decidable-equation-carrier]] (key half paid; a headless carrier's name and UX remain). Combined tree with the parallel display round: suite 1868, 0 failed; bench ok 106. Next per the standing order: [[congruence-by-anti-unification]] — re-read first, its site arithmetic moved twice today.
- 2026-08-18: The order's fourth entry landed as a diagnosis-first round (managed; docs/congruence-in-inference-position-design.md; narrative on [[congruence-by-anti-unification]], which stays open for its layer-m home): the recorded blocker was measured at all 84 library sites and is two-thirds position, one-third computation — a result-only implicit now defers inside trans chains (strictly additive, old path and old message when deferral cannot pay) plus a bounded whnf second attempt in the LGG, but only 7 of 84 sites accept the terse spelling, so the library deliberately keeps its hand spellings with the measurement recorded beside them and the issue's remaining case is the rewriting tactic, now evidenced rather than asserted. Suite 1868 -> 1874; bench ok 106 on the quiet re-run (run 8's nine uniform flags were sibling-round machine load, logged on [[kernel-bench-full-run-flags-drift]]). Residue: [[lgg-diagnostic-dumps-kernel-terms]]. The 2026-08-17 standing order is spent; the next fork is a user call.
- 2026-08-18: Parallel with the congruence round: [[named-arguments]] round one landed (managed round in a worktree; docs/named-arguments-design.md; narrative on the issue, which stays open for half 2): 'f(x := e)' with written order free and elaboration order the declaration's, positional-then-named enforced in the parser, implicits and solver parameters nameable, type parameters deliberately not, constructors nameable by field through the record-literal permuter; calc now names trans's endpoints instead of '@trans'. Defaults-at-binders is staged with its shape pinned (no positional slot, named override) pending the default-body scoping question. Residue filed: [[skel-of-ty-drops-binder-names]], [[partial-type-application]], [[retire-braced-record-literal]], [[named-patterns-by-field]]. The round's own tree: suite 1868 -> 1893, bench ok 106; merged-tree verification recorded in the merge entry below.
- 2026-08-18: Merged-tree verification of the two parallel 2026-08-18 rounds: full scripts/test == suite: 1899 passed, 0 failed == (1868 + the congruence round's 6 + the named-arguments round's 25) and scripts/bench --check ok 106 on a quiet machine — both rounds' claims hold in combination, including their shared crates/elab/src/lib.rs edits.
- 2026-08-18: The fork is called (user): [[calc-equational-chains]] landed and closed (managed round in a worktree; docs/calc-equational-chains-design.md; narrative on the issue). The round's finding: the form already existed and the day-old mechanisms compose to finish it — a calc step is a checking position by construction (named endpoints, 2026-08-17), so the result-only deferral (2026-08-18) makes terse cong(p) the calc-native context spelling with ZERO parser/elaborator change; the §1.2 computation wall stands inside calc exactly as outside, crossed by the author stating the reduct as a refl step; := expr stays the only justification form with ?hole-then-on as the automation seam. Deliverables were the design record, five composed-behavior tests, and eight library towers rewritten as forward-reading chains (statements untouched). Residue: [[calc-over-order-relations]] (mixed =/<=/< chains, shape pinned, trigger = first library proof that stalls wanting one). Suite 1899 -> 1904; bench ok 106 (round tree); merge is content-identical to the round's verified tree, re-confirmed by a full scripts/test on master.
- 2026-08-18: Two residues from the traits/congruence line are paid together: [[designation-key-collides-across-modules]] and [[lgg-diagnostic-dumps-kernel-terms]] closed — designation identity now follows the operand's resolved carrier while diagnostics retain its writable name, and LGG failure crosses the solver boundary as mismatch data for clean surface rendering instead of dumping kernel terms. Suite 1904 -> 1914, verified by a full `scripts/test` on the merged tree (1914 passed, 0 failed).
- 2026-08-18: The next fork is called (user): [[datatype-container-algebras]]' disciplined concrete exploration landed — explicit `ListAlg`/`TreeAlg` values, pointwise uniqueness and fusion, the monoid connection, and a branching/open-type acceptance; no language machinery was needed, and the issue stays open for the now-evidenced generator-vs-container-calculus decision. Suite 1914 -> 1919.
- 2026-08-18: The algebra line continues at its dependent rung ([[datatype-container-algebras]]): explicit `ListElim`/`TreeElim` values and eliminators land, `append_nil` becomes a filled obligation record, and a branching rebuild consumes both IHs. The old [[case-algebra-definitions]] higher-kinded-record blocker is corrected as stale; ordinary value-parameterized record types already suffice. Next evidence points to Cases/open recursion before generation. Suite 1919 -> 1923.
- 2026-08-18: The algebra line's explicit probe is complete ([[datatype-container-algebras]], [[case-algebra-definitions]]): `IrCases` reifies the real interpreter's eight-way dispatch, `step_cases` closes its clauses over the fuel-indexed recursive call, and `step` consumes the table through the generic non-recursive dispatcher; a second consumer and wrong-clause control separate Cases from an interpreter-specific refactor. No language machinery was needed. The explicit `Cases`/`Alg`/`Elim` family is now known; generation is a convenience decision, and the public container calculus remains a distinct mathematical fork. Full `scripts/test`: suite 1923, 0 failed (count unchanged; acceptance extended in place).
- 2026-08-18: The certified-pass algebra probe lands with a split verdict ([[datatype-container-algebras]], [[case-algebra-definitions]], docs/certified-pass-algebra-probe.md): a relation-indexed law record plus one generic induction certifies a genuinely syntax-changing Tree mirror from its Leaf/Node obligations, and a right-branch-dropping mutation is refused locally. The same construction over real `Ir` stops at kernel `OutOfFuel` even specialized to equality; [[ir-pass-dependent-fold-fuel]] owns the measured scale boundary. Architecture validated at branching-library scale, not yet compiler scale; no syntax/generator round follows. Suite 1923 -> 1925, 0 failed.
- 2026-08-18: The certified-pass probe's compiler-scale boundary is paid ([[ir-pass-dependent-fold-fuel]], closed): the exhausted conversion was a value-parameterized law-record projection whose emitted inline Σ annotations disagreed with Γ's component-respelled binder. Fallback projections now keep inline structure for reads but respell emitted `Fst`/`Snd` components. The arbitrary-relation eight-constructor `Ir` induction checks at default fuel; `add(0, tag)` is certified and `Succ(tag)` refused. No kernel or fuel-policy change. Suite 1925 -> 1926, 0 failed; `scripts/bench --check` 106/106. Next value test is semantic execution refinement, still owned by [[case-algebra-definitions]], not generator syntax.
- 2026-08-18: The semantic value test for certified IR passes lands on [[case-algebra-definitions]]: one-slot missing-arm extension changes `NoArm` into an empty-return fallback arm, so the first formerly missing tag demonstrably converges, while the algebra certificate preserves all prior successful evaluations at the same fuel. The compositional relation must pair direct execution with `pick_arm` execution because arm-chain nodes are themselves stuck; this is new evidence about the eventual generated law interface. An existing-arm replacement mutation is refused. Rung 4 is now paid without syntax; constant-match fusion is the next honest optimizer target before a generator decision.
- 2026-08-19: The certified-pass line reaches a real optimizer ([[case-algebra-definitions]], docs/certified-pass-algebra-probe.md): constant-match fusion removes a fresh-slot match whose selected arm and continuation are both `Ret`, explicitly composing field, constructor and arm-output slot maps; successful runs are preserved at the same fuel, a non-empty-field/four-output fixture computes identically, and omitting the constructor-slot shift is refused. The round also corrects the IR design record: landed v1 nodes lack the sketched output arities, so general chain splicing must wait for an arity source rather than guess. No pass syntax or generator machinery was needed.
- 2026-08-20: Named and renamed record/constructor pattern fields landed and
  closed ([[named-patterns-by-field]]), composing with the preceding
  positional `if let` round.
- 2026-08-20: The pattern-line correctness residue
  [[deep-pattern-ctor-needs-column-type]] closed: nested bare constructors are
  classified by their instantiated column type, so an ambiguous import can no
  longer silently turn one into a binder. Suite 1977 → 1978.
- 2026-08-20: [[skel-of-ty-drops-binder-names]] closed: written binder names
  now keep a value-type skeleton even without implicit marks, while anonymous
  arrows remain positional; bench 106/106, suite 1978 unchanged.
- 2026-08-20: [[absurd-at-nat-numerals]] closed: `absurd` now peels matching
  kernel-Nat `Succ` layers until a `Zero`/`Succ` mismatch, so closed numeral
  disequalities use the same one-step surface proof as declared inductives;
  bench 106/106, suite 1978 → 1979.
- 2026-08-20: [[display-inductive-type-arguments]] closed: diagnostics recover
  monomorphized arguments from exact parameter fields only after verified
  re-lowering, and recursive generated shape references invert by registry
  lookup; ambiguous cases retain `<…>`. Bench 106/106, suite 1979 → 1980.
- 2026-09-05: [[ih-generalization]] landed and closed (docs/ih-generalization-design.md): elaborator-computed generalized motives; library uncurried; residue at [[uncurried-recursions-library-sweep]]. Next: [[termination-measures]].
- 2026-09-05: [[termination-measures]] landed and closed (docs/termination-measures-design.md): decreases clauses by strong induction on a Nat bound, obligations as goals or omega; residue at [[mutual-recursion-declarations]] and [[decreases-unfolding-equations]].
- 2026-09-05: Next round chartered (2026-09-05): the termination residue — [[decreases-unfolding-equations]] then [[mutual-recursion-declarations]], one managed round, unfolding first because the group lowering owes the same bound-irrelevance lemma.
- 2026-09-05: [[decreases-unfolding-equations]] landed and closed (docs/decreases-unfolding-design.md): generated f_unfold with generated extensionality and lifted obligations; residue [[unfolding-computed-scrutinee]]. Next: [[mutual-recursion-declarations]] (Part B of the same round).
- 2026-09-05: [[mutual-recursion-declarations]] landed and closed (docs/mutual-recursion-design.md); the round chartered today is complete. Residue: [[group-unfolding-equations]], [[mutual-recursion-measure-synthesis]]; showcase blockers now [[omega-measure-at-constructor-pattern]] and Result/?.
- 2026-09-06: Next round chartered (2026-09-06): [[omega-measure-at-constructor-pattern]], one managed round; the cheaper of the two remaining showcase-parser blockers, Result/? staying a design round on [[prelude-option-and-friends]] layer 2.
- 2026-09-06: [[omega-measure-at-constructor-pattern]] landed and closed (docs/omega-measure-reduction-design.md); the premise was corrected in the design pass (a spelling gap, not a reducer gap). Showcase-parser blockers now: Result/? ([[prelude-option-and-friends]] layer 2) and the rest of [[omega-renders-member-by-base-name]]. Filed: [[tier1-arm-binder-has-no-spelling]], [[lifted-obligation-refusal-reports-retry-error]].
- 2026-09-13: 2026-09-13: the K1 native-bitvector line ([[kernel-native-bitvector-values]]) is complete at three rounds: design, the BitRun word + conversion fast path, and the transducer/consumer classes. Verdict-preserving throughout (miss counts identical), evaluator steps on the closed-word families halved, certificate seconds flat — the seconds on that workload are the typing seam and the literal, not the fold. The line's next lever is [[bitvector-literal-entry-cost]] (a literal born a word; ofNat), then [[bitvector-fold-eagerness-at-demand-driven-consumers]]. Progress items behind x86 (Result/?, showcase parser) are unchanged.

- 2026-09-14: [[result-propagation]] implements the Result/`?` showcase slice with explicit Ok, function/lambda boundaries, and a checked token parser plus recursive collection; Option chaining remains with [[prelude-option-and-friends]].
