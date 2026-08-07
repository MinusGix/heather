---
title: "Meta: frontend roadmap and current focus"
status: open
labels: [frontend,meta]
created: 2026-07-23
updated: 2026-08-07
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
