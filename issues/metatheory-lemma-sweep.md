---
title: Machine-check the stated lemmas of ch. 05/06 (and keep sweeping)
status: open
labels: [kernel,delam,metatheory,testing]
created: 2026-07-25
updated: 2026-07-25
code: crates/kernel/tests/ch05_06_lemmas.rs:1 @ HEAD
---

**Audit: `docs/ch05-06-lemma-audit.md`.** All 53 lemma environments of
`docs/delam/05_…tex` and `06_…tex`, each with its paper location, its kernel
counterpart, and a verdict. **Executable half:
`crates/kernel/tests/ch05_06_lemmas.rs`.**

## Why

[[unit-level-and-vec-preservation]]: `Vec^l(T;0) ⇝ Unit` drops the level,
violating ch. 06's Preservation lemma, and survived three phases of
[[wf-former]] because the suite had `reduction_preserves_type` — the *term*
half of that lemma — and no type half. The witness was generated hundreds of
times per run; the observer was missing.

> Half a stated lemma is a blind spot shaped exactly like its other half.

That claim is only worth anything swept. This issue is the sweep and its
continuation.

## Done

Nine property tests, closing seven paper lemmas or halves. Suite 312 → 322.

| Test | Lemma |
|---|---|
| `conv_relates_type_to_its_whnf` | ch. 06 Soundness (`06:148`), **type half** — missing next to the term half, one lemma before Preservation |
| `whnf_grammar_agrees_with_the_step_relation` | ch. 06 Determinacy (`06:310`,`:319`) — the residue that is not free: `step(t).is_none() ⟺ is_whnf(t)` |
| `reduction_commutes_with_local_substitution` | ch. 06 Local Substitutions (`06:289`) |
| `substitution_interactions_are_functorial` | ch. 05 `lem:dt:interact` (`05:438`), the 3 clauses of 5 that were missing |
| `universe_substitution_preserves_typing` | ch. 05 Universe Substitutions (`05:589`) |
| `local_substitution_preserves_typing` | ch. 05 Local Substitutions (`05:716`) |
| `typing_is_monotone_in_the_layer` | ch. 05 Lifting (`05:996`), the `p → m` arm |
| `inferred_types_are_well_formed` | ch. 05 Presupposition (`05:1446`), in inference mode |
| `the_generator_oracle_holds_across_seed_streams` | not a paper lemma — see below |

## The defect it found is in the suite, not the kernel

`inferred_types_are_well_formed` failed on its **seed 152, first run**: a
generated term that does not type-check. Every property test in the crate
presupposes `gen_wt_term` produces well-typed terms; that presupposition was
checked by exactly one test (`conv_properties::generated_terms_type_check`) at
300 cases on **one** seed stream. Measured rate of violation: **1 in 3000**.

Cause: `TyPi` binds its global type variable at layer `p` and the kernel fixes
that (`typing.rs:575`), so a `TyPi`-bound `U` may never be named at layer `c`.
The generator built the `Δ` of a contextual type at layer `p` — which is what
ch. 04's rule says — so `Δ` could contain `U^δ`, and a layer-`c` body generated
in that `Δ` could lift the entry type into an annotation (a `J` motive, in the
witness). Ill-formed at `c`; **the kernel was right at every step**.

Fixed by generating every `Δ` that hosts a layer-`c` body at layer `c`
(`common/wt.rs`, nine sites). Such a `Δ` is still a valid layer-`p` context by
ch. 05's Lifting lemma — machine-checked as of this round, so the fix rests on
a checked lemma rather than an argument. 0/15 000 across three streams after;
pinned at four streams × 800.

Cost, recorded so it is not rediscovered: `Δ`s containing layer-`p`-only types
are no longer generated. That is the right narrowing — those are exactly the
`Δ`s whose entries cannot legally be reused inside code — but a test that wants
one must build it by hand.

## Next, ranked

1. **Static Code** (`05:1055`) — at layers `v`/`c`, convertibility *is*
   syntactic identity modulo level equivalence. The most load-bearing open gap:
   it is what makes the code eliminator's intensional analysis meaningful, and
   it sits beside the open decision in [[unit-level-and-vec-preservation]].
   Hand-built instances only (`conv::box_compares_syntactically`,
   `conv_pair_properties::box_is_intensional`).
2. **Unlifting** (`05:1039`) and the `c → p` arm of Lifting — needs a layer-`c`
   generator entry point, which the generator fix has made routine.
3. **Global substitutions preserve typing** (`05:1075`) — biggest build cost (a
   *well-typed* `σ` generator; `gen_sigma` is scope-only), biggest coverage
   win, since `σ` is the namespace [[elab-stage2-metas]] lives in.
4. **Reduction under `φ` and `σ`** (`06:280`, `06:298`) — completes the trio
   whose `δ` member is now checked. Cheap once (3) exists.
5. **Equivalent Local Substitutions** (`05:799`) — `wt::perturb_conv` already
   builds the witnesses.
6. **`GlobalSubst::compose`** (`05:377`) — blocked by design, not effort. The
   kernel never composes two global substitutions, so two clauses of the
   algebra and one of `lem:dt:interact` have no implementation to check.
   Decide whether the elaborator needs it *before* adding it, and land the
   algebra laws in the same change.
7. **Transitivity of convertibility** (`06:721`) — reflexivity and symmetry are
   checked; the third PER law is not.

## Two ⊘s worth naming

- **ch. 06 Soundness of the convertibility algorithm** (`06:690`) is the
  largest single unexpressible lemma: the paper proves its algorithm sound
  against a *declarative* equivalence judgment, and the kernel implements only
  the algorithm. Closing it properly means the ch. 07 logical relations, not
  another property test.
- The **global-context equivalence family** (`05:1403`–`:1420`) has no kernel
  data at all.

## Fallout for [[unit-level-and-vec-preservation]]

Candidate **(b)**'s gating question was checked against the paper while
compiling the audit: **no Tarski-completeness claim was found.** `Tarski`
occurs five times in ch. 04 (`04:96–120`, `:203`, `:781`), every occurrence
about the *separation* of types from terms and why Russell-style universes
cannot even state the indices of code — never a surjectivity property. And
ch. 07's term relation at `Ty l` (`07:512–514`) is defined by cases on the code
whnf: it says which codes are related, never that every related type is an
`El`. Evidence, not a verdict — ch. 08's decidability argument is unread, and
so is our own "boxed code stays exhaustively recursable" invariant, which is
ours and not the paper's. Do not implement (b) on this alone.

## Log

- 2026-07-25: Filed with the audit. 53 lemma environments enumerated, nine
  property tests landed (312 → 322 green), one generator soundness bug found at
  a 1-in-3000 rate and fixed. The sweep's own generalization, one level up from
  the [[wf-former]] finding: it is not only *lemmas with halves* — **anything
  the implementation emits and never re-reads is a blind spot**. An inferred
  type, a generated witness, a classification predicate maintained in two
  places. Three of the nine new tests are of exactly that kind, and the one
  defect found was the second kind.
