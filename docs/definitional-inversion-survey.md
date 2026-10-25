# Definitional inversion without normalisation: what it means for Heather

Status: **survey**, 2026-10-25. Source: Carneiro, Coquand, Frabetti Mathieu,
Lennon-Bertrand, Melliès and Weirich, *Definitional Inversion, Without
Normalisation*, arXiv:2607.13662v1 (15 Jul 2026), committed beside this note
as `docs/2607.13662v1.pdf`. Section and page numbers below are the paper's.
Follow-up is in §7.

The paper is about metatheory, not about a prover, so unlike the Arend
survey (`docs/arend-survey.md`) there is nothing here for the language,
tactics or library. Its bearing is on one question Heather has already met:
**which metatheorems about Heather's own kernel can Heather prove about
itself?** The heather-coq port assessment (`docs/heather-coq-port-assessment.md`,
PR #158, open at the time of writing) answered "only the syntactic half, and
the semantic half only for weaker fragments", because of Gödel. This paper
moves a large and useful part of the semantic half to the other side of that
line. Read against master at `6d90690`.

---

## 0. The answer in brief

1. **Injectivity and no-confusion of type formers, subject reduction,
   progress and uniqueness of types do not need normalisation.** The paper
   proves them with a domain-theoretic model and a logical relation whose
   semantic witnesses are *finite* elements (compact elements of a Scott
   domain), in an ambient logic with nothing beyond induction on `Nat`. It
   does so even for `𝒰 : 𝒰` with Π-η, where normalisation is false. Gödel
   does not bite, because none of these results implies consistency (in the
   model, `⊥` inhabits every type).
2. **This corrects the port assessment's §3.2.** That section lists
   "injectivity of formers" among the results that "inherit the limit", and
   notes that preservation's β case needs Π-injectivity, "which only the
   relation gives". After this paper, both can be proved by Heather about
   Heather's full kernel, not only about fragments. Normalisation,
   canonicity, consistency and decidability of conversion still cannot
   (§3 below).
3. **The construction fits Heather's predicativity unusually well.** The
   relation is defined by recursion on finite data (the stage `n` and the
   compact witness), and its universe clause recurses on a smaller witness
   instead of quantifying over relations. So it lives in `Ty 0`: no `∃R`, no
   saturation, no tower of stages at rising levels. The three blockers that
   §3.1 of the port assessment traces to impredicativity do not arise.
4. **The paper's feature list is almost exactly Heather's negative core.**
   Π with η, Σ with surjective pairing, a unit with η, a proof-relevant `Id`
   with no K (the model even refutes definitional UIP), `Nat` with large
   elimination, a universe tower with sort injectivity, and a sub-universe
   of definitionally irrelevant propositions. What it does not cover is
   Heather's distinctive part: DeLaM's layers and `□`, the code recursor,
   `W`/`Wf`/`IWf`, `M`, `sEq`/`sEmpty` and level polymorphism (§4).
5. **Recommendation.** File a research rung under `math-metatheory`: the
   domain-model inversion proof for an MLTTη slice, written in Heather, as
   the first metatheorem Heather proves about a theory at least as strong as
   itself (§6). In parallel, ask heather-coq whether the domain model extends
   to the code layer, which is the one extension the paper gives no evidence
   for. Nothing changes in the kernel.

## 1. What the paper proves

**Object theory (§2).** MLTTη: Π with β and η, and one universe with
`𝒰 : 𝒰`, conversion as a typed judgement. η defeats confluence-based proofs
(Nederpelt's `λx:A.(λy:B.y) x`, Klop's pairs), and type-in-type defeats
normalisation-based ones, so before this paper even subject reduction for
MLTTη was open.

**The model (§2.1–2.5).** A Scott domain `D ≅ [D ⇒ D] + ↑(D × [D ⇒ D]) + ↑1`
(λ, Π, `𝒰`), coalesced so that `λ(⊥) = ⊥`, which is what validates η. One
works almost entirely with its compact elements `C = ⋃ Cₙ`, which have an
elementary inductive description: `⊥`, `U`, `λ(f)` and `Π(a, f)` where `f`
is a *step function*, a finite list of pairs `u ↦ v` (with `λ(⊥) = ⊥` and
presentations of the same step function identified). Semantic typing
`u :ₙ a` on compacts is defined by recursion on `n` (Fig. 2). Types are read
as finitary projectors, terms are interpreted as ideals of compacts, and
soundness (Thm 2.31) says definitionally equal terms denote the same element.
That alone gives disjointness of formers (Thm 2.32): `Π ≢ 𝒰` because the
model's constructors are disjoint.

**The relation (§2.6–2.7).** `Γ ⊨ₙ A ≡ A' type | a` and
`Γ ⊨ₙ M ≡ M' : A | u:a` relate *syntactic* terms, in an open context, along a
compact witness, up to typed head reduction. At `⊥` the relation is
trivially true, like a step-indexed relation at step 0 (the paper calls it a
generalisation of step-indexing to a partial order). At `Π(a, b)` both sides
head-reduce to Π-types with convertible and related components; at `U` both
reduce to `𝒰`, and a term related at `U` is a type related at its own
(strictly smaller) witness. Variables are interpreted by `⊥`, so neutrals are
degenerate and no Kripke quantification over contexts is needed.

**Consequences (§2.8).** The fundamental lemma at witness `Π(⊥, ⊥)` reads off
Π-injectivity directly. Subject reduction and progress follow.

**Extensions (§3).** Universe hierarchies (levels erased in the model; the
relation's `U` clause is sharpened to "both reduce to the same `𝒰ᵢ`", which
yields `𝒰ᵢ ≡ 𝒰ⱼ ⇒ i = j`, cumulative or not), Σ and pairs with η (`(⊥,⊥) = ⊥`),
unit with η (`⋆` is `⊥`), a fixed-point combinator `Y` (no new elements,
`Y F` is the sup of its approximations), `Nat` with large elimination
(`S ⊥ ≠ ⊥`, an observation), `Id` with transport (and `J`), with
definitional UIP refuted by a fitting environment `h ↦ ref ⊥` (Thm 3.1), and
a universe `Prop` of definitionally irrelevant propositions (every
proposition's interpretation is `{⊥}`). The guiding rule (p. 18): the model
may forget anything except what an injectivity result needs and what a later
eliminator inspects.

**Mechanisation (§4).** Agda, Lean and Rocq; Agda and Lean together cover
everything in §3. The Lean version is aimed at Lean4Lean, the Rocq one at
MetaRocq. The formalisations were anonymised for review, so they could not be
read for this survey. Their shape is described: compact elements as an
inductive with step functions as lists of pairs, handled as a setoid rather
than a quotient; strong induction on a rank; in Lean, `Cₙ` by recursion on
`n`, `C` as `Σ n. Cₙ`, and semantic typing **Boolean-valued** by structural
recursion; and in Lean, typing defined as the diagonal of conversion, so one
inductive judgement instead of a mutual pair. The Agda version was written
entirely by Claude under human guidance; the authors report the assistance
grew erratic as proofs became less routine.

**What it does not give (§5).** No normalisation, canonicity, consistency or
decidability. No inversion for neutrals (`x M ≡ y N ⇒ x = y ∧ M ≡ N`),
because neutrals are interpreted by `⊥`. Inductive and coinductive families
beyond `Nat` and `Id` are expected but not done.

## 2. Why it fits Heather

Heather's negative core matches the paper's object theory point for point
(`crates/kernel/DESIGN.md`): Π-η is η-directed comparison, Σ has projections
with η, `Unit^l` has definitional η (proof irrelevance), sums are positive
with no η, `Id`/`J` are proof-relevant with no K, every type has exactly one
level, and universes are not cumulative. These are exactly the features that
make the classical routes hard: η blocks confluence, and Heather's
predicativity blocks impredicative logical relations inside Heather.

Four properties of the construction line up with Heather's design choices.

- **Predicative.** The relation quantifies over terms and compact elements
  only. Its universe case recurses on a witness, not on a stage's relations.
  So Heather can write it as one recursive function into `Ty 0`, with no
  level computed from a `Nat` (the obstacle of the port assessment §3.1).
- **Evaluation as proof.** Compact elements are finite data, their order and
  compatibility are decidable, and the Lean mechanisation already makes
  semantic typing a `Bool` by structural recursion. That is Heather's
  preferred style (prove a closed fact by evaluating a `Bool` to `True`).
- **No quotient needed.** All three mechanisations use an unquotiented
  representation and treat `C` as a setoid. Heather has no quotients and
  uses setoids already.
- **No mutual judgement needed.** Lean's version defines typing as the
  diagonal of conversion. That sidesteps `mutual-inductive-declarations`
  (port assessment §4.1) for a first slice.

## 3. What changes in the port assessment's picture

The assessment's trust split (§11.1 there) is: (1) the checker accepts only
derivable judgements, which Heather can prove, and (2) the rule set is
consistent and normalising, which it cannot. This paper refines the
semantic half into two parts.

| Result about Heather's kernel | Before | After this paper |
|---|---|---|
| Disjointness of formers (`Π ≢ 𝒰`, `Nat ≢ Π`, …) | needs the relation; fragments only | model soundness alone; full kernel, if the model covers it |
| Injectivity of formers, sort injectivity | needs the relation; fragments only | domain-model relation; full kernel, same proviso |
| Subject reduction, progress | needs Π-injectivity | follows |
| Uniqueness of types (one level per type) | needs injectivity | follows (the paper cites it as a consequence) |
| Inversion for neutrals | needs the relation | still not given |
| Normalisation, canonicity, consistency | fragments only (Gödel) | unchanged |
| Completeness and decidability of conversion | fragments only | unchanged |

Two consequences for the ladders:

- **Claim 1 of the trust split gets cheaper.** The assessment notes that
  `AlgSound.v` takes pieces of the declarative congruences from the relation
  (`Validity/Reducible*`), so soundness of the algorithm was on the "needs
  the relation" side. The pieces an algorithm's soundness typically needs
  are inversions: that two Π-types the algorithm compared componentwise were
  convertible componentwise, and that a reduct keeps its type. The paper
  lists kernel verification (Lennon-Bertrand 2025) among its consequences.
  The port thread checked this against heather-coq (port assessment §6, PR
  #158). It looked at every use `AlgSound.v` makes of the
  `DeclConsequences*` lemmas, and they fall into three groups:
  1. Injectivity of each former the algorithm compares, `cpi`/`tpi`/`upi` at
     M included.
  2. Weak-head normalisation, only inside `red_ty_sound`/`red_tm_sound`.
     There it shows that an untyped reduction of a well-typed term is a
     declarative equality, and subject reduction plus soundness of each
     typed step can replace it.
  3. Four layer-M equations: `declM_inst_c_eq`, `declM_inst_t_eq`,
     `declM_motT_eq` and `declM_mott_eq`. These are the CΠ/TΠ instances and
     the recursor's motives at D-convertible arguments.

  `AlgPrereq` itself uses only `gid`/`gsub_wf_gid` from those files. So
  **for the negative core, soundness of algorithmic conversion needs nothing
  the domain model does not give**, and `hih-kernel-model`'s rung 4
  (strategy changes against algorithmic conversion) can be proved sound
  against the declarative rules entirely inside Heather. Group 3 is the
  layer and code-recursor part flagged as open in §4.
- **The reflection schema (§11.2 there) is still needed, but for less.** It
  remains the way to get consistency and normalisation for `Heather≤n`. The
  inversion results need no bound on universes at all, since the model
  erases levels (§3 of the paper, "Universe hierarchies").

A smaller point: the preservation failure recorded in
`issues/unit-level-and-vec-preservation.md` (a well-formed
`Π^{1,0}(_ : Vec^1(T;0)). Nat` stepping to an ill-formed type) is exactly the
kind of defect an internal subject-reduction proof over a faithful rule
table refuses to go through. Today such a defect is found by reading.

## 4. Heather features the paper does not cover

In rough order of risk.

- **DeLaM's layers, `□` and the code recursor.** This is the one place there
  is no evidence either way. Boxed code compares by syntactic equality, and
  `elim_Typ`/`elim_Trm` inspect a code's structure, so by the paper's rule
  (keep what an eliminator inspects) the model needs elements for every code
  constructor, with the recursor's 66 branches interpreted over them. Layers
  and meta-functions over contexts (`CtxPi`/`CtxLam`) have no counterpart in
  any extension the paper treats. A probe in heather-coq is the right first
  step (§6).
- **`W`, `Wf` and `IWf`.** The paper expects "general indexed inductive
  types" to go through (p. 22) and shows `Nat` and `Id`. `W`'s branching is a
  function, so its model element carries a step function of children; that
  is the Π pattern again, and should be routine. `IWf`'s computed child
  indices are not obviously harder.
- **`M`.** Domains are good at infinite objects, and `M` has no η and only
  `out` as eliminator, so the code would be a value constructor like `S`
  whose children are ideals rather than compacts. Not done in the paper.
- **`sEq` and `sEmpty`.** These are the paper's `Prop` pattern: every
  inhabitant is `⊥`, which matches `sEq`'s single proof up to conversion and
  its lack of an eliminator. `elim_sEmpty` eliminating anywhere is
  interpreted by `⊥`. Low risk.
- **Level polymorphism (`UΠ`, level variables).** Levels are erased in the
  model; the relation's universe clause carries the level syntactically.
  Level expressions with variables need the sharpened clause to compare
  levels up to the semantic level equivalence, which is a decision procedure
  Heather would want anyway (port assessment §12).
- **Global definitions with δ.** δ is a conversion rule like β, so it adds a
  soundness case and a head-reduction step, nothing more.

## 5. What this does not change

- **Heather stays total.** The paper's `Y` (§3.3) is a demonstration that
  the method copes with non-termination. Heather's design is evaluation as
  proof, which needs canonicity, which `Y` destroys. No kernel change is
  proposed.
- **heather-coq keeps its relation.** heather-coq proves normalisation and
  decidability, which need the impredicative Kripke relation. This technique
  would be an addition there only as a probe (§6), not a replacement.
- **The no-UIP model stays.** Thm 3.1 refutes *definitional* UIP cheaply,
  but under `𝒰 : 𝒰` propositional UIP is not refutable in this model, so it
  does not replace the groupoid argument of `docs/no-uip-model.md`.
- **The source language of `hih-pl-source`.** A dependently typed source
  with general recursion could have its type soundness proved this way, but
  the effectful source is not dependently typed and its soundness is the
  compiler's correctness theorem, so this is noted, not proposed.
- **Export.** The paper's Lean mechanisation targets Lean4Lean, which would
  strengthen the Lean kernel that `scripts/export-recheck` relies on. That
  is upstream's progress, not work for Heather.

## 6. Proposed work

One research issue, under `math-metatheory` (area `mathematics`), waiting for
a puller, with three rungs:

1. **MLTTη in Heather.** De Bruijn syntax for Π, `𝒰 : 𝒰` and application,
   one typed conversion judgement with typing as its diagonal, the compact
   elements `Cₙ` by recursion on `n` with step functions as lists, semantic
   typing as a `Bool`, and the relation by recursion on the witness. Prove
   Π-injectivity and subject reduction. This is the paper's §2 verbatim, it
   is small, and it is the first metatheorem in Heather about a theory at
   least as strong as Heather. It meets the port assessment's §4.3 (inversion
   at recursive index types) and §5 (automation) at a size where the
   failures are legible, so it is also a cheaper first rung than §9 rung 3
   there.
2. **Heather's negative core.** Add Σ, unit with η, `Nat`, `Id` and the
   universe tower with sort injectivity, and then `sEq`/`sEmpty`. This
   reaches the formers the kernel model already uses (`lib/kernel_model/`),
   so the model's Σ and projections and the copy's inversions speak about
   the same syntax.
3. **Positive formers and the code layer**, after the heather-coq probe
   answers whether the domain model extends to `□` and the code recursor.

That leaves one question for heather-coq: does the domain model extend to
DeLaM's code layer (§4, first item)? It is probe-sized there, and it decides
how far rung 3 can go. Its answer also covers group 3 of `AlgSound.v`'s
needs (§3). The other question, whether `AlgSound.v` needs more than
inversions, is answered: for the negative core it does not.

## 7. Follow-up

Filed:

- [[definitional-inversion-domain-model]] (`mathematics`, `math-metatheory`,
  research): the rungs in §6 and the two heather-coq questions.

Logged on existing issues: `kernel-model` (§3, the bearing on rung 4). The
port assessment's §3.2 and §11 should cite this note once PR #158 lands;
the correction is for that PR's thread to make.
