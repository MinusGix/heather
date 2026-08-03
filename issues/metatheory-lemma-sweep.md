---
title: Machine-check the stated lemmas of ch. 05/06 (and keep sweeping)
status: open
labels: [kernel,delam,metatheory,testing]
created: 2026-07-25
updated: 2026-08-03
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

Eleven property tests, closing eight paper lemmas or halves. Suite 312 → 324.

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
| `code_equality_is_equality_modulo_level_equivalence` | ch. 05 **Static Code** (`05:1055`) — **found a kernel defect**, below |
| `level_equivalent_code_is_convertible` | ch. 05 Static Code, generated companion |
| `the_generator_oracle_holds_across_seed_streams` | not a paper lemma — see below |

## The kernel defect: boxed code was compared too finely

Static Code (`05:1055`) states that at layers `v`/`c` equivalence is equality,
then adds *"All equalities above are quotient over the equivalence of universe
levels"* and gives the example: `Ty (ℓ ⊔ ℓ')` and `Ty (ℓ' ⊔ ℓ)` **as code are
equal**.

`conv.rs` compared boxed code with plain `==`, and `Level` derives `PartialEq`
structurally — so the kernel **rejected the paper's own example verbatim**.
Both sides check at the same `□(· ⊢ Ty (1 + (ℓ ⊔ ℓ')))`; conversion said no.

Incompleteness, not unsoundness — but it contradicts ch. 08's Convertibility
theorem (`08:229`) and would be a spurious error for any universe-polymorphic
metaprogram that built the same code two ways.

**The same shape as the `Vec` bug, one level up**: the implementation read the
lemma's headline (`T = T'`) and not the sentence two lines below saying *which*
equality. Half a lemma again — this time half a sentence.

Fixed with `Type::normalize_levels` / `Term::normalize_levels` (`subst.rs`),
rewriting levels to `LevelNf::canonical` (`level.rs`) through the **existing**
generic traversal rather than adding a third transcription of the syntax.
`conv.rs::code_eq` keeps an `==` fast path.

One thing the test could not pose, which is informative: there is no pair of
codes at *inequivalent levels but the same code type*, because `□(Δ ⊢ Ty l)`
fixes `l` and at layer `c` a type determines its level. Level-sensitivity is
carried by the positives being exactly the ≈-classes, bracketed by
`box (El Nat)` vs `box Nat` and `box (Vec(Nat;0))` vs `box Unit` — the latter
p-convertible through the open `Vec` gap and correctly kept apart as code.

## The other defect is in the suite, not the kernel

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

1. **Unlifting** (`05:1039`) and the `c → p` arm of Lifting — needs a layer-`c`
   generator entry point, which the generator fix has made routine.
2. **Global substitutions preserve typing** (`05:1075`) — biggest build cost (a
   *well-typed* `σ` generator; `gen_sigma` is scope-only), biggest coverage
   win, since `σ` is the namespace [[elab-stage2-metas]] lives in.
3. **Reduction under `φ` and `σ`** (`06:280`, `06:298`) — completes the trio
   whose `δ` member is now checked. Cheap once (2) exists.
4. **Equivalent Local Substitutions** (`05:799`) — `wt::perturb_conv` already
   builds the witnesses.
5. **`GlobalSubst::compose`** (`05:377`) — blocked by design, not effort. The
   kernel never composes two global substitutions, so two clauses of the
   algebra and one of `lem:dt:interact` have no implementation to check.
   Decide whether the elaborator needs it *before* adding it, and land the
   algebra laws in the same change.
6. **Transitivity of convertibility** (`06:721`) — reflexivity and symmetry are
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

Both of candidate **(b)**'s open questions are now closed — see
`docs/ch05-06-lemma-audit.md` §"Two questions settled by reading further" for
the citations.

**1. Nothing requires Tarski completeness; (b) is not blocked.** ch. 08 read in
full: Injectivity (`08:19`), Consistency (`08:48`), Conversion (`08:96`),
Convertibility (`08:226`), Decidability (`08:239`, `:357`) — all structural
induction on derivations, none quantifying over "all types at level `l`".
ch. 07's Neutral Types law (`07:239`) is a closure rule, not completeness.
ch. 04's five `Tarski` mentions are all about type/term separation.

Two things found on the way matter more than the question:

- The paper checks a **layer-`c` global binding's type at layer `p`**
  (`04:~985`, matched at `typing.rs:154`), and ch. 05's coverage lemmas
  conclude type equivalences at `p` (`05:1573`, `:1576`). A layer-`c` term
  legitimately has a layer-`p` type — so (b)'s asymmetry sits in an existing,
  deliberate gap. Better argument for (b) than the one in that issue.
- (b)'s real cost is now nameable and it is *design*, not soundness: it
  falsifies `every_type_has_exactly_one_level` and
  `inferred_level_is_the_only_level` at layers `p`/`m`, and costs
  deterministic level inference at `p` for `Unit`/`Empty`
  ([[elab-unifier-completeness]]).

**2. "Boxed code is exhaustively recursable" was wrong as stated — and the
paper says so.** ch. 06's neutral grammar (`06:31–38`) lists
`elim_Typ(…; box U^δ)` and `elim_Trm(…; box u^δ)` as **neutral forms**, with
the prose *"for the recursive principles, we block on global variables"*.
Global variables are legal at layer `c` and deliberately have no branch. The
kernel was already right (`reduce.rs::is_neutral_term`, pinned by
`recursors_block_on_boxed_global_variables`) and so was
`docs/metatheory-ch07-extensions.md` §8, which annotates both counts with the
blocking note. Only the shorthand in `issues/wf-former.md` and
`tests/wf_codes.rs` overstated it; both corrected, now with the citation.

What made the stronger reading tempting is worth keeping: **ch. 05's coverage
prose closes with "There is no other possible terms at layer `c`"**, which is
true only of the *syntactic formers* — ch. 06 handles the rest. A sentence
from one chapter, read without the neighbouring chapter's grammar.

## Log

- 2026-07-25: Filed with the audit. 53 lemma environments enumerated, nine
  property tests landed (312 → 322 green), one generator soundness bug found at
  a 1-in-3000 rate and fixed. The sweep's own generalization, one level up from
  the [[wf-former]] finding: it is not only *lemmas with halves* — **anything
  the implementation emits and never re-reads is a blind spot**. An inferred
  type, a generated witness, a classification predicate maintained in two
  places. Three of the nine new tests are of exactly that kind, and the one
  defect found was the second kind.
- 2026-07-25: Read ch. 08 in full and ch. 06's normal-form grammar; both questions the audit left open are closed. (1) NOTHING REQUIRES TARSKI COMPLETENESS. Ch. 08's six results (Injectivity 08:19, Consistency 08:48, Conversion 08:96, Convertibility 08:226, Decidability 08:239 and 08:357) are structural induction on derivations; none quantifies over 'all types at level l'. Ch. 07's Neutral Types law (07:239) gives El l v ~ El l' v' FROM the code relation — a closure rule, not completeness. So candidate (b) of [[unit-level-and-vec-preservation]] is not blocked by the metatheory. Two better findings on the way: the paper checks a layer-c global binding's type at layer P (04:~985, matched at typing.rs:154) and ch. 05's coverage lemmas conclude type equivalences at p (05:1573), so a layer-c term legitimately has a layer-p type and (b)'s asymmetry sits in a gap the system already has deliberately — a stronger argument for (b) than 'ch. 04 section 4 is about layer c'; and the LR's only two 'must be unique' appeals (07:761, 07a:1092) are to determinacy of multi-step reduction, never to a type determining its level. (b)'s real cost is now nameable and it is DESIGN not soundness: it falsifies every_type_has_exactly_one_level and the new inferred_level_is_the_only_level at layers p/m, and costs deterministic level inference at p for Unit/Empty ([[elab-unifier-completeness]]). (2) 'BOXED CODE IS EXHAUSTIVELY RECURSABLE' IS WRONG AS STATED, and the paper says so: ch. 06's neutral-term grammar (06:31-38) lists elim_Typ(...; box U^d) and elim_Trm(...; box u^d) among the neutral forms and states 'for the recursive principles, we block on global variables, following [hu2024layered]'. Global variables are legal at layer c and deliberately have no branch, so exhaustiveness is over the SYNTACTIC FORMERS. The kernel was already right (reduce.rs::is_neutral_term, pinned by recursors_block_on_boxed_global_variables) and so was docs/metatheory-ch07-extensions.md section 8, which annotates both counts with the blocking note; only the shorthand in issues/wf-former.md and tests/wf_codes.rs overstated it, both corrected with the citation. What made the stronger reading tempting: ch. 05's coverage prose closes with 'There is no other possible terms at layer c', true only of the syntactic formers — one chapter's sentence read without the neighbouring chapter's grammar.
- 2026-07-25: Static Code (05:1055) closed, and it found the sweep's FIRST KERNEL DEFECT. The lemma says equivalence at layers v/c is equality, then adds 'All equalities above are quotient over the equivalence of universe levels' and gives its own example: Ty(l u l') and Ty(l' u l) as code are EQUAL. conv.rs compared boxed code with plain ==, and Level derives PartialEq structurally, so the kernel rejected that example verbatim — both sides check at the same box(. |- Ty (1 + (l u l'))) and conversion said NotConvertible. Incompleteness rather than unsoundness (we rejected too much, never accepted too much), but it contradicts ch. 08's Convertibility theorem (08:229, syntactic equivalence implies the algorithm accepts) and would be a spurious error for any universe-polymorphic metaprogram that built the same code two ways. Same shape as the Vec bug one level up: the implementation read the lemma's headline (T = T') and not the sentence two lines below saying WHICH equality — half a lemma again, this time half a sentence. Fixed by adding LevelNf::canonical (level.rs) and a NormalizeLevels mapper giving Type/Term::normalize_levels (subst.rs), reusing the existing generic traversal rather than adding a third transcription of the syntax; conv.rs::code_eq is 'a == b || a.normalized() == b.normalized()' so the common case stays allocation-free. Two new tests: code_equality_is_equality_modulo_level_equivalence (hand-built, the paper's example plus idempotence/unit and a reach-under-a-former case, bracketed by negatives) and level_equivalent_code_is_convertible (generated; the level-equivalent twin is built with apply_univ under phi(l) = l u l, deliberately NOT with normalize_levels, which conv uses internally and would make the check circular). One case could not be posed and that is informative: there is no pair of codes at inequivalent levels but the same code type, because box(Delta |- Ty l) fixes l and at layer c a type determines its level — uniqueness of types, the very property [[unit-level-and-vec-preservation]] is about. Consequence for that decision: this does NOT discriminate (a) from (b), which is what I expected it to do. What it does is remove a landmine specific to (a): level-indexed Unit^l/Empty^l puts a level into a layer-c type former, so box(Unit^{l u l'}) vs box(Unit^{l' u l}) would have hit exactly this bug. Suite 322 -> 324.
- 2026-08-03: Priority order set by the ch. 07 FT pass and the user's in-progress **Coq formalization of DeLaM plus our alterations** (the external check this sweep approximates from inside). The pass named its own thin points, so the sweep's next targets are ranked by consumed-through-a-narrow-interface rather than by chapter order: (1) the §19.4 **joinable substitution lemma** for ⇝ₛ — the only statement in the sEq round that differs from what ch. 06 proves (commutes → joins), consumed by everything downstream through exactly one intermediary (07b Reduction Expansion); a property test is statable today (substitute into a strip redex whose side condition the substitution flips, check joinability). (2) **Determinacy of ⇝ₛ** — the complementary-side-condition formulation exists precisely so this holds verbatim; it is one property test and it guards the whole one-rule-plus-one-restriction design. (3) The Part II §13 index lemma stays on the list behind those two. Division of labor with the Coq effort: the property tests here check the *kernel* against the stated lemmas on generated instances; the formalization checks the *lemmas* themselves — where the Coq work lands a result, the corresponding sweep entry records it as discharged rather than re-tested.
