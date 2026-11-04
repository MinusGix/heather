---
title: Well-founded recursion on squashed termination evidence (irrelevant Acc)
status: open
labels: [kernel,delam,design,sprop,research]
area: kernel
created: 2026-10-26
updated: 2026-10-26
---

Heather cannot run a search whose termination evidence is squashed. The
smallest instance is constructive epsilon:

```text
Π(f : Nat → Bool). ∥Σ(n : Nat). f n = true∥ → Σ(n : Nat). f n = true
```

Rocq proves this (`ConstructiveEpsilon`) only through `Acc`'s subsingleton
elimination out of `Prop` into `Type`. Heather has neither half: its `Acc` is
relevant (`docs/acc-via-w.md`), and `squash_ind` eliminates only into a
squash-headed family ([[sprop-squash]]), so nothing turns `∥…∥` into a
relevant `Acc`. Baillon, Forster, Kirst, Mahboubi and Pédrot
(`docs/LIPIcs.FSCD.2026.5.pdf`, §9–10) show that this principle (their
`DAC_{X,N}`, quantifier-free countable choice) is equivalent to `Acc` large
elimination for finitary relations, and that minimal CIC without that rule
proves neither. Heather sits in their minimal setting.

The statement above is a conjecture here, not a checked fact: its
non-derivability in DeLaM with Squash is proposed for heather-coq
(MinusGix/heather-coq#30).

## Who would use it

- **[[default-inhabited-nonempty]] / milestone `math-specific-choice`.**
  `Nonempty<A> → Inhabited<A>` for every `A` is full choice (the FSCD paper's
  Fact 7: a description operator is equivalent to AC). The "specific
  property instead of choice" for a countable carrier is MathComp's
  `choiceType`: from `∥Σx. p x = true∥` with `p` decidable, pick a witness.
  That is constructive epsilon composed with an enumeration, and it is
  exactly what this issue lacks.
- **Evaluators from normalization proofs.** A normalization proof that only
  produces squashed `Acc` (or any squashed `Converges`) gives no evaluator.
  Today termination evidence that someone needs to run has to stay relevant.
  `Converges := Σ(n : Nat). …` (`docs/surface-existential-investigation.md`)
  is relevant, which is the right call under the current rules.

No customer forces the round yet. This issue records the design and its
cost, so that a customer can be weighed against it.

## The design in the literature

Felicissimo, Leray, Pujet, Tabareau, Tanter and Winterhalter, *Definitional
Proof Irrelevance Made Accessible* (LICS 2026, `docs/LIPIcs.LICS.2026.41.pdf`):

- `Acc` lives in the irrelevant sort and eliminates into relevant types
  (rule Acc-el).
- **The kernel's theory (`T=`) has its β rule only propositionally**
  (`acc-el-comp`, an equality proof). Conversion stays decidable, because
  `T=` is CICobs plus new constants and no new equations.
- **A second theory (`T≡`) adds β as conversion.** Its conversion is
  undecidable (Gilbert et al.: under an inconsistent hypothesis every `Acc`
  proof unfolds forever), but it has canonicity, including in the presence of
  irrelevant axioms that hold in their set model.
- **`T≡` is conservative over `T=`** (an ETT-to-ITT-style translation,
  Winterhalter–Sozeau–Tabareau CPP 2019). A proof of an irrelevant goal done
  in `T≡` can be stored in `T=` as an opaque constant without building the
  translated witness, because irrelevant proofs never compute. Rocq exposes
  this as a locally enabled rewrite rule.
- Proof erasure (extraction, or Heather's native compiler) already computes
  as `T≡` does: the evidence is dropped and the eliminator becomes an
  ordinary fixpoint.

## What it would cost Heather

The propositional β is where the design meets Heather's equality.

- In `T=`, `acc-el-comp` is an *observational* equality, whose proofs never
  compute; rewriting along it goes through a type-directed `cast`. Heather's
  `Id` is relevant and `J` computes on `refl`. A primitive `Id`-valued β would
  be a closed stuck proof of an equation, so `J` over it gives closed
  neutrals at any type and canonicity fails.
- An `sEq`-valued β is harmless but cannot be used on a relevant goal, since
  `sEq` has had no `transp` since [[sprop-strip-normalization-open]] (heather-coq
  `M10_DESIGN.md` S8).
- So irrelevant `Acc` with a usable β needs a CCobs-style `cast`: an
  equality that is irrelevant and eliminates into relevant types by
  computing on type structure. That is option (C) of heather-coq's
  `M10_DESIGN.md`, already wanted for indexed families (route 2b). This
  issue is a second customer for the same change, not a reason to make it
  alone.
- The squash side needs one atomic bridge, `∥A∥ → sAcc`, of the kind
  [[sprop-inductives-and-squash-bridges]] already anticipates for `sEq` and
  `sEmpty`: a closed per-former rule whose result shape the kernel checks.
- The `T≡` half (a local scope where β converts, for irrelevant goals only)
  is the same shape as heather-coq's local unfolding scopes
  (MinusGix/heather-coq#51), and its conservativity theorem is the metatheory
  such a scope needs. The kernel itself would stay `T=`; only a proof checked
  under the scope would carry the extra trust, which
  `docs/axiom-provenance-design.md` can report as its own provenance kind.

## Acceptance

- Name a concrete customer (a `math-specific-choice` instance, or an
  evaluator) and the smallest route it needs.
- Decide whether the route waits for a CCobs-style `cast` or there is a
  narrower one (for example, β only at closed, concrete instances).
- Before kernel work, state the ch. 07 obligation: the paper's canonicity
  proof handles `acc-el` on irrelevant evidence by well-founded induction on
  the relation's closed instances (its Assumption B, justified by a set
  model), not by normalizing the evidence. That differs from Squash's
  normalizing-total relation.

## What it assumes from elsewhere

- **[[sprop-squash]]** owns the restricted eliminator. Assumed here: only that
  it eliminates into squash-headed families.
- **[[sprop-inductives-and-squash-bridges]]** owns the bridge decision.
  Assumed here: that a new bridge is a closed per-former rule.
- **[[sprop-strip-normalization-open]]** owns why `transp` left. Assumed here:
  only that `sEq` has no eliminator into relevant types.

## Log

- 2026-10-26: Filed from reading the FSCD 2026 and LICS 2026 papers (both
  PDFs added to `docs/`). Records the gap, the literature's design and where
  it meets Heather's relevant `Id`. No round scheduled.
