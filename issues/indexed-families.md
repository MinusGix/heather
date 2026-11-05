---
title: "Indexed finitary families: how an index reaches the surface"
status: open
labels: [frontend,elaboration,inductives,design]
area: language
milestone: [math-metatheory]
created: 2026-07-26
updated: 2026-09-30
---

`inductive Vec<A> : Nat -> Ty { Nil : Vec<A>(0), Cons(n: Nat, x: A, xs: Vec<A>(n)) : Vec<A>(Succ(n)) }`
— a declaration whose type is a *family*, with the index fixed per
constructor. The surface has no such form: `InductiveDecl` has `params` and
`ctors` and nowhere to write a result index (`crates/syntax/src/ast.rs:47`),
and every tier's lowering assumes the declared type is a single `Ty l`.

## What this issue owns

One claim: **a user cannot declare an indexed family**, and the scheme for
doing so does not exist. Everything else this round touches is owned
elsewhere and appears below only as a named assumption.

## What it assumes from elsewhere

Each line is one assumption on one owner. If the owner moves, this is the
list to re-read — and it is short on purpose, because the first draft
restated these instead of depending on them and went stale within a day.

- **[[nested-inductives-container-fields]]** owns the surface container
  `[T; n]` — its length grammar, its literals, and eliminating one. Assumed
  here: only that `[T; n]` **stays primitive**, i.e. the container in the
  source is the kernel's `Vec`. That is what the withdrawn acceptance
  criterion under *Scope notes* turns on. Nothing here depends on how its lengths parse or on
  which phases of `map`/`fold`/induction have landed.
- **[[wf-former]]** owns `Wf`'s rules. Assumed here: children are a
  `Vec^l(⟦D⟧; n)` with a **single element type**, and a label cannot mention
  its children. The consequence drawn below is ours; that premise is not.
- **[[surface-polymorphism]]** (closed 2026-07-26) owns type parameters.
  Assumed here: an inductive at an **open instantiation** elaborates, so the
  parameter half of `Vec<A>` is not a blocker. If that regresses, the routes below
  are unaffected but the motivating example is unwritable.
- **[[inductive-compiler]]** owns tier classification. Assumed here: its
  scope note that indices are "the same machinery, not a fourth tier" is
  still the intent — the routes below are an attempt to make that true, and if it cannot be,
  that note is what changes.

## The contradiction it has to settle, and which way it now points

[[kernel-v1-extensions]] says inductive families come from **indexed W**.
[[frontend-roadmap]] flagged (2026-07-26) that the branching argument applies
verbatim, and asked for the contradiction to be resolved before a typed IR is
designed.

The claim this issue adds, derived from [[wf-former]]'s premise above and not
available to the first draft because `Wf` postdates [[kernel-v1-extensions]]:

> **`Wf` cannot express indexed W.** Indexed containers need the child type
> to vary per position. `Wf` gives one element type for all children and no
> way for a label to constrain them, so no constructor can fix a child's
> index *structurally*.

Consequence, which is the thing to verify first in any scheme round:
**fording over `Wf` inherits `acc-via-w.md`'s coherence predicate** — a
per-declaration skeleton, `idx` by `elim_Wf`, a code-valued `coh` by
`elim_Wf`, and an `Id` at the top. What `Wf` plausibly buys over `W` is
narrower than the first draft hoped: `coh`'s recursive clause becomes
`Π(i : Fin n). …`, which at a *literal* arity reduces to a Σ-chain with η, so
the funext obligation should disappear exactly as it did for branching. The
`Id`-transport cost looks untouched, and `match` β would be propositional.
**Unverified** — no prototype; `docs/acc-via-w.md` + `crates/kernel/tests/acc.rs`
are the `W` version and the only measured point.

So the contradiction does not resolve to "indexed W" (unreachable from the
current former set) or to "ford over `Wf`" (available, but at tier-2 cost on
finitary data). It resolves to a **classification**, or to a former.

## Routes, none of them costed yet

Written as conjecture. Nothing below has been prototyped; the branching round
is the precedent for what "costed" means (`docs/branching-inductives-choice.md`,
two rounds of postulated-interface tests before the decision).

1. **Index-recursive by large elimination.** When every recursive occurrence's
   index is structurally smaller than the result index, define
   `⟦D⟧ : I → Ty l` by `elim_I` at the large motive, splicing the recursion
   variable's own code for the recursive occurrence — which is verbatim
   `docs/inductive-tier1-lowering.md`'s `D_ex`, a scheme that was written,
   prototyped and kept as a stress suite. No `Wf`, no `Id`, no coherence,
   and β should be definitional for the same reason `cons a l` reduced with
   both variables open: the result index is constructor-headed whatever the
   child is. `Vec` and `Fin` are here; so is a height-indexed balanced tree,
   branching and all.
2. **Ford over `Wf`** — the coherence predicate above. General; tier-2 cost.
   Sharpened 2026-07-28, after a currency correction (see log): the cost
   that decides is not propositional `match` β — that is mechanical residue
   a generator can insert wherever a family is poked — but that forded
   values *store* equality proofs, so value equality needs UIP at the index
   type. At a decidable index (`Nat`) that is Hedberg, a definable lemma the
   generator inserts; at an index without decidable equality there is no
   lemma to generate, and reasoning about the encoded data goes
   setoid-flavored. Plain-`Id` fording is therefore a fallback tier, not a
   candidate general story.

   **2b. Ford over `Wf` with an *irrelevant* index equation.** If the index
   constraint is a definitionally proof-irrelevant strict equality
   (SProp-style — a standing "later" foundations position, which this route
   promotes), the stored-proof hazard dissolves: the proof component cannot
   obstruct conversion, value equality is equality of the visible data, and
   with a `cast` firing on convertible endpoints, β on canonical data is
   definitional as well. Unscored anywhere; couplings worth recording:
   predicativity (already decided) dodges the known normalization failure of
   *impredicative* proof-irrelevant equality, and syntactic box conversion
   (`crates/kernel/src/conv.rs:30`) is the same firewall that contains
   funext, with `Unit`'s irrelevance arm (`conv.rs:789`) as the in-kernel
   precedent for irrelevance coexisting with the code layer. The strict-Prop
   round now has an owner: **[[sprop-strict-prop]]** (filed 2026-07-28, off
   this route) — the couplings above live there; assumed here is only that
   an irrelevant `sEq` with a convertibility-firing `cast` arrives.
3. **Per-constructor fording inside route 1.** A constructor whose index
   pattern does not determine its children's indices
   (`Node(l: T(m), r: T(k)) : T(Succ(plus(m,k)))` — `Succ`-headed, but
   `plus(m,k)` is not invertible) takes `Σ(m, k). Σ(Id; plus(m,k); p). …`
   *in that one branch*. If this composes, the "how much `Id`-transport
   survives" question the round is supposed to answer has a syntactic answer
   per constructor rather than an empirical one. **Whether it composes is
   the first thing to check.**
4. **An indexed `Wf` former** — children at per-position indices via a
   dependent vector `DVec(f : Fin n → Ty; n)` by `elim_Nat`, which is Σ-based
   and so keeps η. Named because "change the former set" was the right answer
   to the branching question (`docs/branching-inductives-choice.md` §15) and
   route (b) there was dismissed too early. Not a recommendation.

## Scope notes

- **`TyKind::Vec`/`ExprKind::VecLit` do not retire, and the first draft was
  wrong to make that the acceptance criterion.** Two owners say so and this
  issue defers to both: [[wf-former]], because `Wf`'s typing rule mentions
  `Vec`; and [[nested-inductives-container-fields]], whose primitive-container
  assumption above a declared `Vec<A>(n)` would violate. A defensible
  criterion is "a declared family behaves as well as `[T; n]` does", not
  "`[T; n]` becomes a declaration".
- **Parameters vs indices** must be stated in the scheme even though neither
  half is blocked: a parameter is uniform across constructors and lowers by
  substitution; an index varies per constructor result and is what every
  route is about.
- **Why before the IR.** [[ir-simulate-design]] and [[datarepr-separation]]
  are the motivating consumers, but the feature is not IR-specific and doing
  it *for* the IR would bake IR-shaped assumptions into general machinery.
  This part of the first draft stands.
- **Not in scope, and previously conflated:** mutual declarations (no scheme
  at any tier), and nested occurrences, which are [[nested-inductives-container-fields]].

## Log

- 2026-07-26: Opened, off the [[frontend-roadmap]] flag that
  [[kernel-v1-extensions]]'s indexed-W claim contradicts the branching
  decision.
- 2026-07-27: REWRITTEN, because the original was stale within a day of being
  filed and asserted more than it had. Three premises corrected against the
  tree rather than dropped quietly: vector lengths are expressions, not
  literals (ast.rs:214); the surface *can* eliminate a vector since
  container-fields phases 2–3; and [[surface-polymorphism]] closed, so the
  parameter half is not a dependency. The acceptance criterion (retire
  `TyKind::Vec`) is withdrawn as wrong, not deferred: `Wf`'s typing rule
  mentions `Vec`, and container-fields §1 turns on the surface container
  *being* the kernel one. One new load-bearing fact the original could not
  have had, since `Wf` postdates `kernel-v1-extensions`: `Wf` cannot express
  indexed W at all, because its children are a `Vec` with a single element
  type and a label cannot mention its children — so fording over `Wf`
  inherits `acc-via-w.md`'s coherence predicate, and the contradiction
  resolves to a classification or a former rather than to either horn. Routes
  restated as four unprototyped conjectures with the composition question in
  route 3 named as the first check. Nothing here is measured; the branching
  round's standard for "costed" is the bar.
- 2026-07-27: Tracker review, same day: this issue's rewrite was the trigger for three ownership rules now in issues/README.md, and for backlink printing in scripts/issue. Nothing about the design changed.
- 2026-07-28: Currency correction, from discussion: the bar is not
  "definitional or bust" — residue the elaborator can mechanically generate
  when a family is poked is acceptable; setoid-like contamination is not.
  Under that bar, route 2's real defect is the stored index proof (UIP at
  the index type; a cliff at non-decidable indices), and route 2b — fording
  with an SProp-style irrelevant equality — is the contender no prior scoring
  saw, coupling this issue to the strict-Prop foundations position. Two
  further discussion outcomes, both conjecture: route 1 is not Nat-specific
  (large elimination over any declared inductive index works, so
  subject-recursive judgments like typing derivations are route 1, and the
  non-route-1 remainder shrinks to intrinsically-indexed syntax and
  computed-value indices); and route 3's composition check is expected to
  fail (the recursion code exists only at the predecessor index and an `Id`
  does not relocate it — course-of-values is the rejected code-tables
  encoding of `docs/branching-inductives-choice.md` §10).
- 2026-07-28: SProp decided (discussion): [[sprop-strict-prop]] filed and owns the strict-Prop round; route 2b's couplings move there. Route 1 is agreed as the near-term scheme (its own round, unblocked by SProp); the general case waits for SProp, then 2b-vs-route-4 by prototype. Route 4 stays the measured fallback.
- 2026-07-29: Route 2b setoid acceptance prototype DONE: crates/elab/tests/indexed_route_2b.rs (9 tests, four-axis discipline, full suite green). Forded Vec = Sigma(s : List). sEq(Nat; len s; m) over the tier-1 skeleton with len eliminator-computed, constructors carrying the index equation as an sEq payload field pushed through S by transp; eliminator = skeleton recursion at Q(s) = Pi m' e. M[m', <s,e>] with per-constructor inversion of the motive's index by elim_Nat (no-confusion arms transp into Empty via zero_pred/is_succ; the successor arm re-derives the tail's proof by transp-at-pred). Results against the bar: (a) match beta is DEFINITIONAL on open recursive data (n, x, xs all variables) including at an open element code — the stored proof is consulted nowhere and lands only at sEq positions (irrelevance arm) and inside repackagings (Sigma-eta); (b) value equality is lemma-free — proof-swapped values convertible outright, the cross-index-spelling transport lemma is literally refl, and the route-2 hazard is pinned as a contrast (Id-stored proofs make the same comparison fail); (c) mismatched indices genuinely reject, including the axis-4 quotient control. Two findings. (1) Definitional open-data beta NEEDS the index inversion, available exactly when the constructor's result index is constructor-headed — route 1's condition resurfacing inside 2b; at a non-invertible index (route 3's plus(m,k)) the transp-only eliminator still types and equality stays lemma-free, but open-data beta degrades to strip-guarded (definitional only where endpoints convert). Mechanical residue under the 2026-07-28 bar, not setoid contamination. (2) The strip is head-only (Conv::strip): a cast at convertible endpoints strips as a value but is OPAQUE to elimination (elim cast /= elim payload, pinned as a negative) — harmless because such casts are exactly the unnecessary ones (bare values already check at either index spelling and beta fires through it), so the generator rule is: never emit a cast at convertible endpoints. VERDICT on 2b-vs-route-4: 2b passes the setoid bar with zero new kernel machinery beyond the landed SProp round; route 4 (an indexed Wf former = a full former round at the Wf-landing yardstick) buys nothing the bar demands and stays the unexercised fallback. Caveat carried, not hidden: the skeleton here is tier-1 (Vec does not branch); the fording layer never inspects the skeleton's recursion, but Wf-skeleton composition — fording plus branching plus the coherence question — is the one untested corner of the general scheme.
- 2026-07-30: Route 1's round scoped: docs/inductive-indexed-lowering.md, scheme before prototype before generator per the tier discipline. The scheme is inductive-tier1-lowering.md's D_ex with the user's index in place of the synthetic height: family by elim_Nat at motive Ty l, one branch per index-constructor class, pattern-variable fields elided from storage (they ARE the elim binder — 2b's inversion insight in its native habitat, with the inversion machinery gone because the eliminator recurses on the index directly). Classification: depth-one linear constructor-headed result indices, recursive fields at pattern variables only; everything else rejected toward 2b/fording with the measured facts named. Two things the doc claims that the prototype must earn: branching is FREE (Node(l: T(n), r: T(n)) : T(S n) splices El rec twice — the §8.1 max-computation failure of exact-height fording does not arise because the index is given, not computed), and cross-class no-confusion is vacuous (the type rejects the equation). Scope: single Nat index this round; declared index types stated as an instantiation (§8.2), not a redesign. Next: hand prototype (checklist §9), then parser+classifier+generator.
- 2026-07-30: Route 1 hand prototype DONE, same day as the scoping: crates/elab/tests/indexed_route1.rs (12 tests, first-run green, negatives engaged). Vec at an open element code, Fin, and the branching Tree, all as kernel terms against the real kernel. The doc's three load-bearing claims all held: (a) beta fires on fully open data (element code, index, element, tail all variables) and the arm recovers the pattern variable as the elim_Nat binder with zero inversion machinery; (b) BRANCHING IS FREE — Node(n, l: T(n), r: T(n)) : T(S n) is in constructor form with both children open, mirror beta-fires through it, and mirror(mirror t) = t goes through by induction with two J's; exact-height fording's §8.1 wall (the stuck height comparison) never appears because the index is given, not computed; (c) cross-class no-confusion is vacuous (the Id types are ill-formed) and within-class no-confusion is tier 0's tag predicate inside the branch, verbatim. Also measured: append at Vec(plus n m) with open indices — the arm obligation Vec(plus (S n) m) ≡ Vec(S (plus n m)) is definitional, in checking position. Remaining in the round: the generator (parser, classifier, lowering, surface match), doc §9 item 8.
- 2026-07-30: Route 1 GENERATOR landed, same day as the prototype: a user can now declare an indexed family. Surface (crates/syntax): `inductive Vec<A> : (n: Nat) -> Type { Nil : Vec<A>(0), Cons(n, x, xs: Vec<A>(n)) : Vec<A>(Succ(n)) }`, with `Vec<A>(e)` in type position riding the existing applied-type-is-never-called backtracking (it arrives as an expression; the elaborator recognizes the family application before the generic decode path). Elaborator (crates/elab/src/indexed.rs): family form El(elim_Nat(_.Ty l; base; step; e)) per the scheme doc; constructors check the written index by one conversion against the expected family's and then read every annotation off the whnf'd branch spine (tier-0 build_fields reused verbatim, pattern-var arg dropped); match is elim_Nat with a class case tree per branch, the motive generalized over a variable index (synth_motive's swap-substitution device, one binder deeper), an explicit two-binder motive form (`as λ n z => T`), and Fin(0)-style matches falling to the Empty path by whnf. Self-calls: GuardKind::Wf reused (children = spine projections, ih = rec child), plus one new notion — Guard.rebind: the index parameter must be passed as the arm's pattern variable, relaxing the every-other-arg-unchanged rule by exactly the one argument the ih re-fixes. Acceptance: crates/elab/tests/indexed_families.rs (8 tests) — len/peek/append with open-data refl proofs, cmap_id and mirror-involution by surface induction (j + recursive theorem calls at the rebound index), all §8.1 rejections pinned by message; full workspace suite green (47 binaries). One hazard for the record, caught by the kernel gate as a LevelMismatch: never shift a family's step code detached from its elim_Nat node (its m/rec binders read as free). Remaining on this issue: the 2b generator for the general case, declared (non-Nat) index types (doc §8.2 — an instantiation, not a redesign), multi-index (§8.4), and indexed absurd/inj surface forms (doc §7) when something needs them.
- 2026-07-30: Follow-up, same day: doc sec 10 records the known seams (indexed_of's structural fingerprint, the pre-reduced-type gap, per-occurrence term size, the duplicated arm walk with its third-variant-extracts rule), and the sec 9 level gap is closed: fields_above_level_zero (a Type-valued field, family at level 1, motive at 0) caught two real level bugs on its first run — the match eliminator's elim_Nat level must be the motive Pi's join, not mlvl, and elab_check's type-position bridge must whnf before giving up (an indexed spine's components are El(TmTy ...), a universe hiding under El). Both fixed; 47 binaries green. Lesson recorded in the doc: uniformly-level-0 suites cannot see a dropped join, so every new family-form consumer keeps one nonzero-level test.
- 2026-07-29: Status note, same day: the issue stays OPEN — what landed is the acceptance prototype and the 2b-vs-route-4 decision, not the feature. A user still cannot declare an indexed family; the remaining work is route 1's own round (agreed 2026-07-28 as the near-term scheme) and the 2b generator for the general case, both against the scheme this prototype validated.
- 2026-07-30: §8.2 hand prototype DONE, first-run green (crates/elab/tests/indexed_declared_index.rs, 9 tests): declared index types ARE an instantiation of route 1, not a redesign. Three index shapes against the real kernel — an enum (family by Case at motive Ty 0; no recursion expressible, and the classification says so by shape), a linear Wf index (a declared Nat-clone: family by elim_Wf at motive Ty 0, recursive field code = ih at a Fin literal), and a branching Wf index carrying a derivation-shaped family (Bal over Shape — the subject-recursive-judgment miniature; both ihs from one threaded ih at different Fin positions, β through the branching index constructor with everything open). Four facts the Nat round could not show, recorded in doc §8.2: the refined-arity device (cs/ih threaded through the Case motive — wf.rs's own §6.2 device at motive Ty l), Unit η newly load-bearing on the INDEX side (branch-rebuilt sup_f(inl u; cs0) ≡ the declared constructor by η at Unit, twice), pattern variables recovered as nth(cs', i) ≡ child projections (no inversion), and branching free per-position. The 2026-07-28 conjecture is now measured, not conjectured: subject-recursive judgments (typing derivations indexed by terms) are in route 1's fragment. Remaining: the generator plumbing (declared index head in the classifier, Case/elim_Wf family builder, projection-recovered pattern variables in the arm walk, one nonzero-level test).
- 2026-08-01: **The classifier's uniform-bare-variable arm is corrected**, by the [[surface-existential]] round. A result index that is a bare variable in *every* constructor is not an index at all — it is uniform, hence a **parameter**, and it lowers by substitution with none of this issue's machinery (no fording, no stored equation, no Wf skeleton, no UIP, no Id-transport). The diagnostic used to send exactly that case toward route 2b; it now says "a **parameter**, not an index" and names the grammar that exists for it (`record D(n: Nat) { … }`, docs/surface-value-parameters.md). The *non-uniform* case — some other constructor pins its index — keeps the old fording message unchanged, because that one really is the general case. Both arms pinned in crates/elab/tests/indexed_families.rs. Nothing about this issue's scope moves: the parameters-vs-indices line stated in its own scope notes ("a parameter is uniform across constructors and lowers by substitution; an index varies per constructor result") is confirmed against the tree, not revised — only the message that was steering people across it.

- 2026-08-03: §8.2 GENERATOR landed (managed round): a user can now declare a family indexed by a *declared* inductive, not only `Nat`. `IdxTy { Nat, Decl }` with `Nat`'s constructors numbered like any other index's (the primitive case stops being special); family builder dispatches `elim_Nat` / `Case` tree / `elim_Wf`, the `Wf` case through wf.rs's own `build_elim_wf` via a new `Branches::Custom` variant so the §6.2 refined-arity threading exists once; arm walk recovers pattern variables as `nth(cs'; ι_t)` (children) or label projections (payload arguments — a widening of §8.2 fact 3, recorded in the doc). Acceptance: crates/elab/tests/indexed_declared_families.rs, 14 tests over the three prototype shapes (enum, linear Wf, branching derivation-shaped) with per-positive negatives and the §10.5 nonzero-level case; full workspace suite green. Two scheme corrections folded into the doc at §8.2 facts 1/3 (the family threads cs AND ih — a payload field at a recursive pattern variable needs `nth(cs')`; flat-index payload pattern variables); index-type restrictions recorded (un-parameterized, unindexed, no container fields, ≥2 constructors — the last so §10.1's fingerprint has a `Case` node to key on); `Guard.rebind` reshaped to one index term per descendant. Seams: §10.1 and §10.3 amplified (three family head shapes with a fueled tag search; `elim_Wf` families are large per-occurrence terms), one new §10.6 (index type must survive as a declaration — alias-hostile). The 2026-07-28 conjecture is now shipped, not just measured: subject-recursive judgments are declarable at the surface. Remaining on this issue: the 2b generator for the general case, multi-index (§8.4), indexed absurd/inj (§7) when something needs them.
- 2026-08-03: Scope note from the ch. 07 FT pass ([[metatheory-ch07-sprop]], §22.4): the 2b generator's rule "never emit a cast at convertible endpoints" must be read as covering **index and code positions** (a transp inside a `Vec`/`Wf` length or an `El` argument), not only value-level casts — the head-only strip gap has a type-former face there (`docs/sprop-design.md` §5.4 correction; pinning tests at [[seq-strip-type-former-negatives]]). The landed route-1 generator does not emit such casts; the 2b generator, when written, inherits this as a stated rule rather than an accident.
- 2026-08-03: Route 2b SCHEME + PROTOTYPE landed (managed round; generator deliberately not started). docs/inductive-fording-lowering.md is the general case's scheme doc, sibling of route 1's; crates/elab/tests/indexed_route_2b_wf.rs (11 tests, full workspace green) is its prototype, one branching Rope vehicle with an invertible AND a computed constructor. Scheme: skeleton = the declaration with indices erased, lowered by the unindexed tiers verbatim (so a recursive family's skeleton is a Wf, always — the 2026-07-29 caveat understated this: since tier1-wf-lowering sec 9 retired exact-height fording, the Wf skeleton is the only skeleton, not a corner); measure mu : Skel -> I by the skeleton's own eliminator, each branch the constructor's written result index with child-index variables replaced by the recursion at that child; family Sigma(s : Skel). sEq(I; mu s; m); constructors pair the skeleton with proofs pushed through by transp (all at sEq, hence invisible); eliminator = skeleton recursion at Q(sigma) = Pi m' e. M[m', (sigma,e)], per constructor form A (invert the motive's index) or form B (one transp at the arm's head). Classification widens: computed result indices, deep patterns, non-linear patterns, non-uniform bare-variable indices all become generatable; three new rejections (F1 child index must be a variable, F2 linear, F3 no payload type mentions a child index), each because the missing constraint would need acc-via-w.md's coherence predicate. THE UNTESTED CORNER IS CLOSED: fording over a Wf skeleton composes with no new machinery and NO coherence predicate — nothing stores an index, so nothing can disagree with the data — measured on the branching Rope at an open payload type and at level 1; F1/F2 are measured restrictions, not caution (the falsifier hand-builds the shared-child-index measure and exhibits the quotient value it admits). FINDING (1) of 2026-07-29 IS MEASURED, AND PARTLY WRONG: the transp-only eliminator types and keeps equality lemma-free, but its beta is NOT strip-guarded and 'open data' is the wrong key — form B computes exactly when the stored proof whnfs to srefl (measured firing on fully open data with a srefl proof; measured stalling on the same data with a neutral proof, residue a stuck App(transp ...) the head-only strip never reaches, ch07 sec 22.1's elim(cast) shape in a new position); form A is definitional on open data exactly at a constructor route-1-eligible on its own. Also a witness for ch07 sec 22.3's honest limit: the generator emits no redundant cast, but beta-reduction manufactures one at the arm redex, so the cast rule is necessary-and-not-sufficient. Remaining: the 2b GENERATOR (doc sec 13.2 items 8-14 — a route-1-generator-sized round, stopped before rather than half-wired), multi-index (sec 8.4), indexed absurd/inj (sec 7).
- 2026-08-04: Route 2b GENERATOR landed (managed round): a user can now declare the general case — computed result indices, deep patterns, non-uniform bare-variable indices — closing doc §13.2 items 8–14 in full. crates/elab/src/forded.rs (FordedFam, forded_of's tag-anchored fingerprint, build_mu over both skeleton shapes, the §7 transp constructor chain, elab_match_forded with form-A/form-B arms); the §3 total classifier in inductive.rs (classify_indexed_route/classify_forded, F1–F3 with §3.3's wording); acceptance crates/elab/tests/indexed_route_2b_gen.rs, 17 tests, four-axis discipline with a deliberate form-B negative. Suite 891 → 908. Four route-1-era rejections became elaborations (computed index, deep pattern Ev, non-uniform bare variable, non-linear index *expression* — behaviour changes, assertions moved in the route-1 suites). Deviations, each pinned: form A is Nat-only and exactly F2's one-child-at-Succ shape (§8.2's phrasing suggested a generality F2 already forbids); item 9's recursive theorem is by cases not induction, because Tm's constructors are all form B — the SHARPER FINDING, now in doc §8.4: a declaration all of whose recursive constructors are form B admits no induction over open data at all (arm goals stuck App(transp …) on both sides); the mixed rejection also fires for a single constructor failing both routes, naming both reasons. HIGHEST-VALUE FIND, a pre-existing route-1/tier-1 bug: wf_case_tree's inner Inr annotations shifted d+1 where the substitution says two binders past cx (same closure shared by idx_case_tree/indexed_case_tree) — kernel LevelMismatch, never a wrong answer, invisible at ≤2 constructors or a closed payload; fixed, and docs/testing-generated-terms.md gains axis 6 (case-tree emitters need ≥3 constructors crossed with axis 2). Two new seams in doc §14 (items 7/8: type-argument inference does not reach forded constructors — the common forded shape has no bare-parameter field; forded_ctor_index infers payload arguments on the infer path). F2 clarified in §3.3: non-linear index expressions are legal, only shared child-index variables reject. Remaining here: multi-index (§8.4/route-1 §8.4), indexed absurd/inj (§7), form A at a declared index (doc §14.4 — every declared-index forded family is form B everywhere until composed), forded families as written type arguments.
- 2026-08-04: Form A at a DECLARED index landed (managed round; the §14.4 seam closed): the inversion is carried by the index type's own eliminator — Case tree at a flat index, elim_Wf at a recursive one — no-confusion via wf.rs §7.1's tag predicate, child indices recovered by transp through §7.2's child_projection. Hand composition first per the tier discipline (forded.rs's decl_inversion module, 4 tests, no scheme-level surprise), then arm_form generalized (Form::ADecl); acceptance crates/elab/tests/indexed_route_2b_declared.rs (9 tests, axes stated per test, incl. axis 6's ≥3-constructor × open-payload control). Suite 908 → 924. So a declared-index forded family is no longer form B everywhere: induction whose step is at an invertible constructor CLOSES (an_induction_whose_step_is_a_form_a_constructor_closes), with the form-B stall kept as a pinned contrast. Rider also landed: type-argument inference for forded/indexed constructors where a CHILD argument determines the instance (lib.rs ctor_from_child — the child's type IS the family, re-indexed by ty_at/el_at, nothing unified), plus written instantiations for nullary constructors (Leaf<Nat> via ctor_at); the undetermined case's message now names both escapes — the §14.7 seam narrowed to parameters occurring only under a field's type constructor ([[elab-unifier-completeness]]). CLASSIFIER DEFECT FOUND AND FIXED: all_bare_var_indices (inductive.rs) read a nullary index constructor as a bare variable (Tw(SLeaf) parses as App(Tw,[Var])), so every enum-indexed forded family with one bare-variable constructor got the parameter message instead of fording; fixed by excluding the index type's constructor names, pinned by a_nullary_index_constructor_is_not_a_bare_variable. TWO MEASURED BOUNDARIES, both in doc §14: (1) §14.8 — form A is NOT generated when the index constructor has a payload argument (TS(n,x) : Tg(CS(n))): the field is stored in the skeleton, and the arm would have to choose between the stored and inverted values, related only by the irrelevant sEq — §8.2's route-1-eligibility rule overpromised there; (2) §14.9 — a branching index constructor at a three-constructor index puts the emitted eliminator (one child_projection per child + one tag predicate per other constructor, each a whole elim_Wf, fns inlined per use) over DEFAULT_FUEL in conversion at 2×; both factors needed, pinned as a deliberate negative, retired together with §14.2's μ-inlining by a kernel def. ALSO MEASURED, new §8.4 text: a theorem equating FAMILY VALUES (map(s,d) = d) closes at no index, Nat included — every forded declaration has ≥1 form-B constructor by construction and the goal there sits under the arm's own transp; smallest case two childless constructors. Minor: at a declared index a uniform bare-variable index gets route 1's generic message rather than §3.3's 'parameter, not an index' row (Nat-only in parse_result_index) — rejection correct, message asymmetric. Remaining: form A at a payload-argument index constructor (§14.8), the kernel-def size/fuel cut, value-equation induction, multi-index, indexed absurd/inj.
- 2026-08-04: The kernel-def round ([[generated-term-defs]], landed and closed today) reaches this issue in three places: (1) §14.9's fuel cliff is GONE — the branching-form-A-at-a-three-constructor-index negative flipped positive and is rewritten as such, so the boundary recorded 2026-08-04 morning no longer exists; the bench suite gained a forded/declared-index-branching family (slope 1.53). (2) §14.1's fingerprint seam closed by re-keying — and was two-sided: the old structural forded_of would have accepted a Σ over F's skeleton carrying G's μ, building a constructor of F whose equation was about G; both directions now pinned (forded.rs mod fingerprint). (3) §14.2's μ-inlining closed for unparameterized families; a PARAMETERIZED family's μ stays inlined (registration needs a closed body; the monomorphized skeleton isn't known at declaration time) — a real but narrow residue, one family in the suite. The residual cost story moves to [[family-types-as-code-defs]].
- 2026-08-05: 2026-08-05: Route 1's size lever now has a spec and a deferral, from [[family-types-as-code-defs]] (closed today): docs/family-type-code-defs-design.md §6 defines the family-function definition D#fam : Trm_c(· ⊢ Π(i : I). Ty l) := λi. elim(…; i), occurrence El l (D#fam^δ @ i), same gate and boundary (unparameterized only), with indexed_of re-keyed in the same motion (nominal branch through the registry; forded.rs mod fingerprint's El-headed negatives are the template, including the two-real-declarations forgery). That round is a SUCCESSOR owned here — route-1 §10.1/§10.3's amplification history lives in this log, and §10.3's 'a kernel def is the eventual fix' resolves to D#fam. Nothing was touched this round: indexed_of and route-1 emission are unchanged, its structural fingerprint keeps working (verified: full suite green through the forded re-key). A route-1 swept bench family does not exist yet; adding one is part of that round's acceptance, or an explicit decision not to (design §8 phase 5).
- 2026-08-05: Defect found and fixed by the [[dependent-motive-crossing-sweep]] round (2026-08-05): `forded.rs::ctor_spine_at` re-lowered the skeleton at **no type arguments** (`lower_instance(cx, skel, &[], …)`), so a field spelled `A` resolved against a fresh instantiation that never bound it — every parameterized forded family with a *non-recursive* skeleton was unusable at its first constructor use (`unknown type \`A\``, a resolver message from inside the generator). Invisible because the suite's parameterized forded family (Tree<A>) has a recursive skeleton and its non-recursive one (Any) is monomorphic: the two conditions were each tested, never crossed. Fix reads the spine out of the already-lowered `skel_ty`; regression test `a_parameterized_family_over_a_non_recursive_skeleton_is_usable`. The forded lowering's inner-injection shifts themselves were audited correct and are now pinned by mutation-verified controls.
- 2026-08-06: Route 1's D#fam round LANDED (managed round; design §6 / §8 phase 5, the successor owned 2026-08-05): every unparameterized route-1 family registers D#fam := λ(i:I). elim(…; i) through the same best-effort gate (all three head shapes; a declared index's IdxCode rides along, its 2b-only devices deliberately not), occurrences are El l (D#fam^δ i) from the one emission site (lower_indexed_instance), and indexed_of gained the nominal branch with the fueled structural search kept live for exactly the two spellings that still arrive inline — parameterized families (§5) and pre-unfolded occurrences (§4, pinned with a conv_type between the spellings). indexed.rs mod fingerprint (6 tests, forded.rs's template incl. the two-real-declarations forgery and the byte-identical-global negative) plus a level-1 four-axis fixture; suite 1093 → 1100, full scripts/test green. Route-1 doc §10.1 CLOSED, §10.3 measured: new indexed/arms bench family (route 1 had none) — constant ~1.10×, exponent 2.20 → 2.25 unmoved; the Θ(n)-per-arm residue is the CLASS type, which no def names — the next lever named there. HEADLINE MISATTRIBUTION FIXED: forded/declared-index-tags was never forded (pattern indices, classifier tries route 1 first — no skeleton, no μ, no inversion); route 1's lever moved it 2.79 → 2.22 (2.5× at 6), so two rounds' explanations of its flat exponent were arguing from the wrong family — fording doc §14.11 corrected, [[wf-shape-annotation-slots]] now rests on declared-index-branching alone. Baseline deliberately NOT re-recorded (already red on master from ~10 commits of drift, machine at load 5-7 / Tctl 95°C); bands tightened in fixture sources, indexed/arms stays untracked until a quiet-machine --save. NEW DEFECT FOUND, pre-existing: level-heterogeneous classes are kernel-rejected at every use — filed as [[route1-class-level-join]], writeup at route-1 doc §10.5.
- 2026-08-06: Status note (updated 2026-08-10): open deliberately — the 'landed' entries are slices (latest: route 1's D#fam). Remaining as listed 2026-08-04/05: multi-index (§8.4), indexed absurd/inj (§7), form A at a payload-argument index constructor (§14.8), and value-equation induction. The level-heterogeneous class defect is closed by [[route1-class-level-join]].
- 2026-08-06: Route 1's APPLICATION-side gap (logged 2026-08-04: len<A>(n, v: V<A>(n)) applied at a concrete instance cannot solve A because unify_ty finds nothing structural in El(elim ...)) was CLOSED EN PASSANT by [[type-arg-inference-through-index]] (closed 2026-08-05), not by the unifier-completeness round that went looking for it (docs/unifier-completeness-design.md §5.5): unify_tm's ElimNat and type-code-constructor congruences are exactly the missing structure, plus the kernel-def round's D#fam re-keying for the unparameterized class. Both the open-data and constructor-literal probes elaborate and kernel-check (capped runs, 2026-08-06).
- 2026-08-10: Route 1's level-heterogeneous class defect closed — [[route1-class-level-join]] now builds every class at the family join and pins the asymmetric level fixture.
- 2026-09-30: Route 4, extended with an output-index function, is proposed to replace route 2b: [[iwf-former]] (`docs/iwf-former-design.md`). 2b's `transp` turned out to cost UIP for `Id`, plus an open normalization question ([[sprop-strip-normalization-open]]).
- 2026-11-05: gardener: cites a file it shares with [[conv-query-identity-env-per-gamma]] (`crates/kernel/src/conv.rs`); [[conversion-typed-eliminator-congruence]] (`crates/kernel/src/conv.rs`); [[elab-emits-normal-form-of-matched-type-argument]] (`crates/elab/src/forded.rs`); [[interval-paths-for-funext]] (`docs/sprop-design.md`); [[iwf-inversion-recursive-index]] (`docs/iwf-former-design.md`).
