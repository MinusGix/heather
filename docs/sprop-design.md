# `sEq`/`transp`: strict equality and definitional irrelevance in the kernel

Status: **reviewed 2026-07-28, rule set frozen** (§8 steps 1–2 done; no
kernel code yet). The ch. 07 sketch is part III of
`docs/metatheory-ch07-extensions.md`; its two findings were folded back
into §5.2/§7 below, and the review pass confirmed the §5.2 placement
against `conv.rs:522–527` (`tm` whnfs the type and both terms, then
dispatches on the type — the strip loop slots into the term-whnf stage).
Written per the wf-former discipline (`docs/wf-former-design.md` is the
template and the precedent). Tracking issue: `issues/sprop-strict-prop.md`;
promoting customer: `issues/indexed-families.md` route 2b (fording's index
equation must pass the setoid test).

Reference point: Gilbert–Cockx–Sozeau–Tabareau, *Definitional
Proof-Irrelevance without K* (GCST) — the unlayered version of most of what
follows. Predicativity is already decided (impredicative Prop rejected
2026-07-23), which keeps us clear of the Abel–Coquand failure mode.

The design principle, stated once: **irrelevance is a property of fixed
formers, not a classification of types.** The kernel never asks "is this
type a proposition"; it has conversion arms for the formers that are one.
Everything below — the missing sort, the derived closure rules, the absence
of relevance marks — follows from that.

---

## 1. Sort structure: there is no third sort

The issue's decision 1 assumed the spelling "a separate sort `SProp^l` with
no cumulativity into `Ty`" and left open how it lands in the layered
grammar. Answer, after checking what a sort *costs* here: **it doesn't land;
the kernel gets no new sort.** Propositions are spelled as ordinary `Typ`
formers with definitional-irrelevance arms in `tm_nf` — the `Unit` pattern
(`conv.rs:789` @ 0f3e24b, `crates/kernel/DESIGN.md` third extension),
which has already survived a ch. 07 round.

Why the judgmental sort was declined, costed:

- **The grammar is two-sorted and everything is threaded per-sort.** Ch. 04
  defines exactly `Typ` and `Trm` (04, the syntax display), and every piece
  of layered machinery exists once per sort: contextual types (`□(Δ ⊢ Ty l)`
  / `□(Δ ⊢ T @ l)`), global binders (`U : Typ…` / `u : Trm…`), the code
  recursor's motive vector and branch vectors (`M_Typ`/`M_Trm`,
  `b̄_Typ`/`b̄_Trm`), the five parallel transcriptions. A third sort
  multiplies all of it and lands squarely in ch. 07 territory nobody has
  layered. That bill buys one thing: a kernel-checked classification of
  *user-defined* propositions — and users cannot define kernel formers, so
  for a fixed former set the classification classifies nothing.
- **The customer needs propositions *inside* `Ty` anyway.** Fording puts
  `sEq(Nat; n; length …)` into a constructor's Σ-payload — a relevant
  type. A genuinely separate sort with no cumulativity would need an
  explicit embedding former just to state the forded payload; the
  "firewall" would have a mandatory door, in every generated constructor.
- **What the sort was protecting is protected without it.** "No
  cumulativity into `Ty`" was shorthand for *irrelevance must not leak into
  relevant conversion*. Per-former arms cannot leak: `Nat` has no arm, and
  there is no generic rule keyed on a sort for a wrong type to slip
  through. The invariant survives as: **the set of irrelevant formers is
  closed and enumerated in this document** — extending it is a design
  round, not a subtyping rule.

What replaces the closure rules ("Π from `Ty` into `SProp` lands in
`SProp`"): they hold as **theorems of the existing checker**, not as rules.
`tm_nf` at a `Π` compares by applying both sides to a fresh variable at the
codomain type (`conv.rs:535`-adjacent arm, unconditional full η); if the
codomain is an irrelevant former, that recursive comparison hits its arm
and accepts — so any two inhabitants of `Π(x:A). sEq(…)` are already
convertible. Σ-closure likewise via Σ-η and projections; `Unit` is already
irrelevant. The class of definitionally irrelevant types is closed under
Π, Σ, Unit, `sEq`, `sEmpty` *compositionally*, with zero new closure code.
This is the same move as `Wf` storing children where η already reaches:
irrelevance is stored where the η family already recurses. (Testable, and
§8 tests it.)

Consequently there is also **no `SProp^l` hierarchy** to design:
`sEq^l(I; a; b) : Type @ l` sits in the one hierarchy that exists, and
predicativity is inherited rather than restated. Agda's `Prop ℓ` precedent
becomes moot. If a surface `Prop` classifier ever arrives, it is an
elaborator classification (the elaborator already owns the policy that
`sEq` stays generator-internal and `Id` is the surface `=`); the kernel is
not involved.

> **Related implementation evidence** (found 2026-07-28, after freeze;
> non-normative). Sirman–Lennon-Bertrand–Krishnaswami, *Implementing a
> Type Theory with Observational Equality, Using NbE* (TYPES 2024,
> DOI 10.4230/LIPIcs.TYPES.2024.5) implement CCobs's `cast(A, A', e, t)`
> and independently corroborate three of this document's calls. (1) Their
> strip (`cast(A, A, e, t) ≡ t`) lives in conversion checking, not
> reduction: "treating this rule as a reduction breaks determinism … more
> worrying, it makes reduction and conversion checking mutually
> recursive" — the withdrawn "punctures" claim and its resolution, in
> print. (2) Their completeness remark — eagerly applying Cast-Eq-Left/
> Right loses no solutions, because when strip and congruence both apply
> all four types are convertible — is §5.2's "strip is rewrite-by-
> equation" argument; note their bundled three-rule formulation
> backtracks, while the per-side strip loop here needs no backtracking,
> and their own remark is the proof. (3) Via Pujet's thesis §5.2.2:
> canonicity's *sole* constraint is that casts between convertible
> *closed* types compute — β-on-srefl satisfies it, and the rest is
> design freedom. Two of their pain points are taxes this kernel never
> pays: untyped term-directed conversion broke transitivity at their unit
> type (`x ≡ ! ≡ y` but `x ≢ y`) where our type-directed `tm_nf` arms are
> total, and they burned two designs on the irrelevant *semantic domain*
> (proof erasure cannot quote; syntactic props entangle evaluation and
> quoting) — an NbE-specific cost; a whnf-based syntactic kernel keeps
> proofs as ordinary syntax that comparison skips. Their cast computes on
> *type structure* (CCobs); ours β's on `srefl` (GCST) — deliberate, per
> §4.

---

## 2. New formers

Two type formers, mirroring existing ones field-for-field. Both are
extensions beyond DeLaM ch. 04, `kernel-v1-extensions` style.

### 2.1 `sEq` — strict equality (the customer)

```
Γ ⊢ I : Type @ l     Γ ⊢ a : I     Γ ⊢ b : I
----------------------------------------------
Γ ⊢ sEq^l(I; a; b) : Type @ l
```

`Type::SEq { level, ty, lhs, rhs }` — field-for-field the shape of
`Type::Id` (`term.rs:56` @ 0f3e24b), and deliberately so: `sEq` is `Id`
minus proof relevance plus strictness. Encoding `TmSEq` mirrors `TmId`
(`sEq^l(s; t; u) : Ty l` with `s : Ty l`; `El` decodes), carrying its level
so the code determines its type — the lesson of
`docs/unit-empty-level-indexing.md` is baked in from day one.

Layer treatment: `sEq`/`srefl`/`transp` are MLTT formers like `Id`/`J` —
type formers mismatch outside layer m, term arms locally bump the layer to
m (the `conv.rs` header discipline). Nothing layer-novel.

### 2.2 `sEmpty` — absurdity with an invisible proof

```
--------------------------
Γ ⊢ sEmpty^l : Type @ l
```

Level-indexed like `Unit`/`Empty` (same load-bearing reason: every type has
exactly one level). Irrelevant (any two terms at `sEmpty` convertible —
vacuously sound, the type is uninhabited in consistent contexts) and
eliminating anywhere: `elim_sEmpty^{l,l'}(M; e) : M` for any
`M : Type @ l'`, neutral on a neutral `e`, no β (nothing canonical to fire
on) — `Empty`'s eliminator discipline verbatim.

*Alternative considered:* reuse `Empty` and upgrade its structural-neutral
arm (`conv.rs:796`) to irrelevance. Sound, and saves three rec branches —
but it retroactively changes the definitional equality of every existing
`Empty` client and re-opens its settled ch. 07 case, to save less than
`Fin` would have. Declined for the same reason `Fin` was kept: symmetry and
a restriction-shaped LR case are worth two branches. **Shed-weight
candidate** if the round runs heavy, exactly like `Fin` was (§1.2 of the wf
doc): make `Empty` irrelevant instead and drop `sEmpty`; nothing else in
this document depends on the choice.

Deferred, unchanged from the issue: squash `∥·∥` (needs its restricted
eliminator designed), SProp inductives in general.

---

## 3. Introduction

```
Γ ⊢ I : Type @ l     Γ ⊢ a : I
--------------------------------
Γ ⊢ srefl^l(I; a) : sEq^l(I; a; a)
```

`Term::SRefl` mirrors `Term::Refl` field-for-field. Fully annotated,
synthesizes. It is also the *only* canonical form at `sEq` — which is what
makes β sufficient in §5.

---

## 4. Elimination: `transp`

Not OTT-style cast between types: transport along a term-level `sEq`
through a motive — J's non-dependent cousin (issue decision 2, corrected
2026-07-28).

```
Γ ⊢ I : Type @ l     Γ, x : I ⊢ P : Type @ l'
Γ ⊢ a : I    Γ ⊢ b : I    Γ ⊢ e : sEq^l(I; a; b)    Γ ⊢ t : P[a/x]
-------------------------------------------------------------------
Γ ⊢ transp^{l,l'}(I; x.P; a; b; e; t) : P[b/x]
```

Fully annotated, synthesizes — the eliminator discipline of `J` and the
box-synthesis-gap constraint. No `sJ` (motive over the proof) exists or is
needed: proofs are irrelevant, so `transp` plus the irrelevance arm derive
it, and UIP at `sEq` is definitional by construction —
`p ≡ srefl : sEq(I; a; a)` is the §5.1 arm firing, not a theorem.

The K-avoidance shape is GCST's: `transp` never matches on the proof's
structure, only β's on the constructor, so the equality is strict without
importing K's pattern-matching pathology.

---

## 5. Reduction and conversion

The three-piece decomposition (issue decision 2), each piece landing where
the kernel already puts that kind of equation. Nothing punctures the
reduce/conv separation.

### 5.1 `reduce.rs`: β only

```
transp^{l,l'}(I; x.P; a; b; srefl^l(_; _); t) ⇝ t
```

Fires on the constructor whatever the annotations are, like every β. No
conversion query in reduction. Sufficient for closed computation by
canonicity: a closed proof of `sEq` whnfs to `srefl`, so kerneltime
functions on forded data never stall on a `transp`. Same shape as J's β.

`elim_sEmpty`: no β (no canonical form).

### 5.2 `conv.rs` `tm_nf`: irrelevance arms and the strip rule

**Irrelevance arms** — the `Unit` pattern, verbatim:

```rust
Type::SEq { .. } => Ok(()),      // any two proofs convertible
Type::SEmpty { .. } => Ok(()),
```

**The strip rule** — the load-bearing novelty. On a side whose whnf has a
`transp` head, run a *guarded* query on that transp's own endpoints; if
they convert, the transp is invisible:

```
whnf(s) = transp(I; x.P; a; b; e; t)     a ≡ b : I @ l   (guarded)
------------------------------------------------------------------
s ≡ t' ⟸ t ≡ t'
```

Well-typed by `P[a] ≡ P[b]`. This covers what β cannot: a *neutral* proof
(a hypothesis `e`) at endpoints that are nonetheless convertible —
`plus(0, n) ≡ n` with `n` open — which is exactly what makes forded casts
invisible on open data, the property 2b's setoid test demands.

Guard semantics, settled against `Conv`'s actual state (@ 0f3e24b; full
argument in the issue log 2026-07-28):

- **Catch `NotConvertible`, propagate `OutOfFuel`.** Those two are the
  whole error enum (`conv.rs:69`). A caught NC means "take the neutral
  path", the first conv query whose failure is not a verdict. Exhaustion
  is global — the shared budget is spent — and must propagate.
- **No fuel refund.** `Conv { fuel: u64 }` is the entire mutable state
  (`conv.rs:240`); monotone-decreasing fuel *is* the totality argument
  (`conv.rs:41–45`). The failed query's spend is real work.
- **No backtracking hygiene.** A successful strip rewrites by a proven
  equation, not a choice point — eager stripping never loses
  completeness; a failed guard has mutated nothing but fuel. Future
  memoization stays coherent because the guard is an *ordinary* query
  caught at the call site, not a query mode (standing constraint either
  way: never cache `OutOfFuel`).
- **Placement — term-head-keyed, unlike the type-keyed η family.** A
  stuck transp sits at *any* type `P[b]`, so strip cannot be a `Type::…`
  arm. It is a whnf-adjacent loop per side, before type dispatch: whnf;
  if transp head and the guard succeeds, replace by the payload and
  re-whnf. Each strip pays `spend()` — morally a conversion-level
  reduction step, fitting the documented fuel model; termination is the
  payload being a strict subterm. The guard query runs at the stripped
  transp's own `I : l` annotations — the loop is per-side, so there is
  no left/right choice here (left-bias belongs only to §5.3's
  congruence arm). One wasted-but-sound corner, accepted: at an
  *irrelevant ambient type* the terms get whnf'd and possibly
  guard-queried before the `Ok(())` arm fires, since `tm` whnfs terms
  ahead of type dispatch (`conv.rs:522–527`) — correct, just not free;
  not worth restructuring `tm` over.
- **The guard is the algorithmic mirror of a declarative premise.**
  The strip rule's declarative form carries the side condition
  `Γ ⊢ a ≈ b : I` (part III §19, finding 2 — the premise must be
  declarative convertibility, *not* semantic relatedness, or the LR
  goes circular by levels). So ch. 08-style completeness for the guard
  has the usual shape; no new proof-obligation kind.
- **Fast path:** syntactic `==` on the endpoints before the full query
  (the kernel already owns that comparison for boxed code).

### 5.3 `tm_ne`: congruence keyed on endpoints, not the proof

Two stuck transps compare componentwise — and the arm **inverts J's
discipline**. J compares its proof structurally (`conv.rs:1231`, `tm_nee`)
because the proof is the scrutinee and neutrality is keyed on it; transp's
stuckness is keyed on the *endpoints* (the guard failed), so two stuck
transps over different neutral proofs must still be equal:

- `I`, `P`, `a`, `b`, `t` compared typed, at their §4 types (motive under
  `Γ, x : I`, payload at `P[a]`, left-biased);
- the proofs compared at `sEq` type — where §5.2's arm accepts, i.e. the
  recursion is skipped. One uniform principle (SProp-typed comparisons
  succeed), no relevance marks threaded through the congruence rules.
  Synthesized type: `P₁[b₁/x]` at `l'₁`, J-arm style.

`elim_sEmpty` neutrals: motive typed, proof skipped (same principle).

### 5.4 Derived facts, no extra rules

- `Vec(D; transp(e, n)) ≡ Vec(D; n)`: neutral `Vec` types compare
  componentwise on lengths *as terms*, where the strip fires. Stuck
  type-level reduction needs no help.
- Derived transports through type formers (the OTT cast lemmas) are
  conversions here, not lemmas: a transp at a Σ/Π/Vec motive strips
  whenever its endpoints convert, and stays a well-behaved neutral
  otherwise.
- Π/Σ-closure of irrelevance: §1, via the existing η arms.

---

## 6. Codes and the meta layer

Decided in the issue (decision 4): SProp enters the code layer; encodings
live in types metaprograms see.

```
TmSEq    { level, ty: code, lhs: term, rhs: term }   El(TmSEq …) ⇝ SEq(…)
TmSEmpty { level }                                   El(TmSEmpty) ⇝ SEmpty
srefl / transp / elim_sEmpty — ordinary terms that become code when the
layer gate lifts (the `sup_f` precedent: no new enum variants, only
branches).
```

`TmId` is the precedent for codes containing terms; `TmUnit`/`TmEmpty` for
level-carrying nullary codes. The □-firewall is untouched: boxed code
compares syntactically (`conv.rs:30`), so two definitionally equal proofs
remain distinguishable *as code* — intended semantics, same as funext
containment (issue, "well-positioned" §).

Code-recursor bill (`rec.rs`, W-landing yardstick): `ty_seq`/`tm_seq`,
`ty_sempty`/`tm_sempty`, `tm_srefl`, `tm_transp`, `tm_elim_sempty` —
**7 branches, 45 → 52**, `tm_transp` deepest (six subterms, two levels —
comparable to `tm_elim_w`). Plus the usual five parallel transcriptions
(rec.rs, subst depths, reduce β, `BRANCH_DIMS`, `identity_branches` ×2,
`gen_branches`). Dropping `sEmpty` (§2.2 alternative) saves 3 branches.

---

## 7. Metatheory (ch. 07) obligation — the abort criterion, stated before code

Own round, per the issue's sequencing note: postulates cannot de-risk a
*conversion* feature, so this document plus the ch. 07 sketch are the
de-risk. GCST did the LR unlayered; nobody has done it layered.
**Sketch done 2026-07-28**: part III of `docs/metatheory-ch07-extensions.md`
(§§18–22). Results, against what this section predicted:

- **`sEq`/`sEmpty` as predicted**: Id's type rule + Unit's total term
  relation, escape from the irrelevance *laws* (which is why they are
  declarative laws), everything else vacuous.
- **The strip closure came back different than predicted** (part III
  §19): a per-type closure clause is wrong — a stuck `transp(e; 5)` at
  `Nat` is a whnf that must relate to `5`, which no neutral clause can
  give. The uniform fix is an **evaluation-notion edit**: the LR reads
  term relations over whnf-*then-strip* normal forms — the exact
  semantic counterpart of §5.2's whnf-adjacent loop. Global but uniform:
  the first extension round that edits a shared notion instead of adding
  cases. Second finding: the strip premise must be *declarative*
  convertibility (§5.2 above), or the relation is circular by levels.
- **The □/code observers argued, not just flagged** (part III §20): §6's
  Id-round warning about "an irrelevant/definitional-Id rule" is
  defused — irrelevance collapses the proofs, not the endpoints, and
  endpoint checking still goes through conversion-at-□ = `==`. `sEq(Ty
  l; A; B)` is inert as expected: it observes definitional encoding
  equality, which `Id` at `Ty l` already observes propositionally.
- **Pre-code verdict: the abort criterion is not triggered** — no
  relevance marks anywhere. The standing risk that survives the sketch:
  the evaluation-notion edit touches every term-relation case, and the
  sketch re-read them for shape, not in full; the with-code FT pass is
  what retires it.

**Abort criterion:** if the layered LR cannot state the strip closure
without threading relevance marks through context entries or the
congruence rules (i.e., if "irrelevance as per-former arms" fails
semantically where it succeeded syntactically), the design *reverts to the
judgmental sort* (§1's declined alternative) and this document gets
rewritten — the GCST fallback, at the cost §1 itemizes. Same discipline as
the `Wf` round: criterion on paper before the first kernel line.

---

## 8. Sequencing and acceptance

1. ~~**This document reviewed** and the rule set frozen.~~ Done
   2026-07-28; review deltas: §2.1 layer note, §5.2 per-side/left-bias
   correction and the declarative-premise point, placement confirmed
   against `conv.rs:522–527`.
2. ~~**ch. 07 sketch** (§7) *before* kernel code~~ Done 2026-07-28 —
   part III of `docs/metatheory-ch07-extensions.md`. Abort criterion
   **not** triggered pre-code; the evaluation-notion risk is carried to
   step 3's with-code FT pass.
3. ~~**`sEq`/`srefl`/`transp` land** with conversion tests that exercise the
   four axes of `docs/testing-generated-terms.md`~~ Done 2026-07-28 —
   `crates/kernel/tests/seq_transp.rs` (14): strip on a *neutral* proof at
   convertible endpoints (`plus0(n) ≡ n`, open `n`), strip in a *checking*
   position, negative controls (distinct endpoints don't strip; `srefl`
   rejected there), proof-skipping congruence, iterated strip, definitional
   UIP, and the fuel sweep (every insufficient budget dies `OutOfFuel`,
   never as a verdict). One perf finding, fixed in-round: the strip check
   must live inline in `Conv::tm` (one discriminant read), not in a
   whnf-wrapping helper — the extra `Term` moves cost 1.35× on
   `conv/computed-numeral`; `scripts/bench --check` is what caught it.
4. ~~**Derived-closure tests** (§1)~~ Done, same file: two inhabitants of
   `Π(x:Nat). sEq(…)` convertible with no new code;
   `Vec(Nat; transp(e,k)) ≡ Vec(Nat; k)` through the neutral-`Vec` arm.
5. **`sEmpty` + rec.rs round** (§6), or the §2.2 shed if heavy.
6. **Acceptance — the 2b setoid test**: a forded constructor whose payload
   carries an `sEq` field, where (a) `match` β fires on open recursive
   data through the strip, and (b) value equality on the forded data costs
   no `Id`-transport lemmas. Route 2b's prototype
   ([[indexed-families]]) is the customer that signs off.
