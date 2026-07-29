---
title: "Indexed finitary families: how an index reaches the surface"
status: open
labels: [frontend,elaboration,inductives,design]
created: 2026-07-26
updated: 2026-07-28
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
