# The ch. 05/06 lemma audit

*What DeLaM states, what the kernel checks, and where the gaps are.*

Every lemma, theorem and corollary of `docs/delam/05_syntactic_operations_and_properties_of.tex`
(**53** environments across both chapters, of which 2 are commented out in the
source) is listed below with its paper location, its counterpart in the kernel
test suite, and a verdict.

## Why this exists

Phase 4 of [[wf-former]] found that `Vec^l(T; 0) ⇝ Unit` drops the level, in
violation of ch. 06's *Preservation* lemma. The witness had been generated
hundreds of times per run since phase 1. What was missing was the **observer**:
`conv_properties.rs` had `reduction_preserves_type` — the *term* half of the
lemma — and no type half.

> **Half a stated lemma is a blind spot shaped exactly like its other half.**

That is a claim about a *class* of defect, not about one reduction rule, and it
is only worth anything if the class gets swept. This document is the sweep.
Its executable half is `crates/kernel/tests/ch05_06_lemmas.rs`.

## How to read the verdicts

| | Meaning |
|---|---|
| **✅** | Machine-checked by a property test over generated witnesses. |
| **◐** | Checked only by hand-built instances, or implied by a property that is strictly stronger in one direction and silent in the other. |
| **○** | **Open gap** — stated in the paper, expressible against this kernel, not checked. |
| **—** | Holds by construction of the implementation; there is nothing for a test to falsify. |
| **⊘** | Not expressible: the kernel has no data for the judgment (or no such operation), so the lemma has no implementation-side reading. |

A **⊘** is not a free pass. Several are load-bearing absences and are called
out individually.

---

## Chapter 06 — Reduction and Convertibility

| Paper | Lemma | Verdict | Kernel counterpart |
|---|---|---|---|
| `06:148` | **Soundness** — `T ⇝ T'` ⇒ `T ≡ T'` (types) | ✅ | `ch05_06_lemmas::conv_relates_type_to_its_whnf` *(new)* |
| `06:148` | **Soundness** — `t ⇝ t'` ⇒ `t ≡ t'` (terms) | ✅ | `conv_properties::conv_relates_term_to_its_whnf` |
| `06:264` | **Preservation** — types, at the same `l` | ✅ | `conv_properties::type_reduction_preserves_level` — *live, with one narrow documented skip* (see [[unit-level-and-vec-preservation]]) |
| `06:264` | **Preservation** — terms | ✅ | `conv_properties::reduction_preserves_type` |
| `06:280` | Reduction commutes with **universe** substitution | ○ | — |
| `06:289` | Reduction commutes with **local** substitution | ✅ | `ch05_06_lemmas::reduction_commutes_with_local_substitution` *(new)* |
| `06:298` | Reduction commutes with **global** substitution | ○ | — |
| `06:310` | **Determinacy**, single step | — | `step_type`/`step_term` are functions: a redex has one reduct. |
| `06:319` | **Determinacy**, weak head normal form | — | `whnf_*` iterates `step` to a fixed point. |
| `06:310`/`:319` | *the residue that is **not** free* | ✅ | `ch05_06_lemmas::whnf_grammar_agrees_with_the_step_relation` *(new)* |
| `06:690` | **Soundness of the convertibility algorithm** (9 clauses) | ⊘ | See note below. |
| `06:711` | `W ≈ W'` (nf) ⇒ `T ≈ T'` | ◐ | Structural in `conv.rs`; exercised by `conv_relates_*_to_its_whnf`. |
| `06:721` | PER (commented out; postponed to the LR) | ◐ | Reflexivity ✅; symmetry ✅ (both orientations, in the `whnf` laws); **transitivity ○**. |

**On the two Determinacy lemmas.** Both hold by construction, and saying only
that would be a dodge. What the lemmas *presuppose* is not free: the normal-form
grammar `W ∪ V` must be **exactly** the non-stepping types. Disagree in one
direction and `whnf` returns something that still reduces, so conversion
compares a redex; disagree in the other and `whnf` spins until it burns fuel.
`reduce.rs` holds two independent copies of that condition — `step_type`
(`:73`) and `is_whnf_type` (`:1791`) — and for `Vec`/`Fin` the condition is
"the length is stuck", which phases 1–3 edited. The new property asserts
`step(t).is_none() ⟺ is_whnf(t)` at every point along a reduction sequence, and
that neutrals are a sub-grammar of the normal forms.

**On `06:690`.** The paper proves its *algorithm* sound against its
*declarative* equivalence judgment. The kernel implements only the algorithm —
there is no second, declarative `≡` for it to be sound against — so the lemma
has no direct reading here. It is proxied, not replaced, by
`conv_is_reflexive_on_well_typed_terms`, the two `conv_relates_*_to_its_whnf`
laws, and the perturbed-positive / mutated-negative pairs in
`conv_pair_properties.rs`. Worth stating plainly: **this is the largest single
⊘ in the audit**, and closing it properly means the ch. 07 logical relations,
not another property test.

---

## Chapter 05 — Syntactic Operations and Properties

### Algebra of substitutions

| Paper | Lemma | Verdict | Kernel counterpart |
|---|---|---|---|
| `05:320` | `id`/`∘` of universe substitutions are well-formed | — | `φ` is a `Vec<Level>`; nothing to falsify. |
| `05:330` | **Algebra of Universe Substitutions** | ✅ | `subst_laws::universe_identity_and_composition` (assoc of `∘` on `φ`: ◐) |
| `05:345` | `wk`/`id` local substitutions are well-formed | ◐ | `subst_laws::local_identity` |
| `05:354` | **Algebra of Local Substitutions** | ✅ | `subst_laws::local_{identity,composition,composition_associative}` |
| `05:371` | `wk`/`id` global substitutions are well-formed | ○ | — |
| `05:377` | **Algebra of Global Substitutions** | ◐ **+ ⊘** | Identity ✅ (`global_empty_is_identity`). **Composition and associativity are not expressible: `GlobalSubst` has no `compose`.** |
| `05:395` | **Acting on Weakenings** (`lem:dt:wkact`) | ○ | Indirectly exercised by `subst_laws::global_local_commute_weakening_focus`. |
| `05:431` | **Acting on Identities** (corollary) | ○ | — |
| `05:438` | **Interactions** (`lem:dt:interact`), 5 clauses | ✅ | 2 by `subst_laws::{universe_local,global_local}_commute`; the remaining 3 by `ch05_06_lemmas::substitution_interactions_are_functorial` *(new)* |

**`05:377` is a real absence, not a bookkeeping one.** The kernel never composes
two global substitutions — it only ever applies one — so two clauses of the
algebra and one of `lem:dt:interact` have no implementation to check. That is
fine *today*. It stops being fine the moment the elaborator instantiates a
global under another global (metas-as-Ψ-globals: [[elab-stage2-metas]]). Adding
`GlobalSubst::compose` without these laws would be adding an unchecked
operation to the most delicate namespace in `subst.rs`.

### Typing under substitution, and layers

| Paper | Lemma | Verdict | Kernel counterpart |
|---|---|---|---|
| `05:589` | **Universe Substitutions** preserve typing | ✅ | `ch05_06_lemmas::universe_substitution_preserves_typing` *(new)* — the `T`/`t` clauses; the Ψ/Γ/equivalence clauses ◐ |
| `05:669` | **Partial Presupposition** (`lem:dt:presup1`) | ⊘ | Judgment-shaped; the kernel has no equivalence-of-contexts data. |
| `05:691` | Symmetry and transitivity of local substitutions | ⊘ | No public convertibility on substitutions. |
| `05:702` | **Reflexivity** | ✅ / ◐ | Terms ✅ (`conv_is_reflexive_on_well_typed_terms`); **types ◐** — reflexivity at a whnf only. A dedicated `conv_type` reflexivity law is a two-line gap. |
| `05:716` | **Local Substitutions** preserve typing | ✅ | `ch05_06_lemmas::local_substitution_preserves_typing` *(new)* |
| `05:799` | **Equivalent Local Substitutions** (`lem:dt:lsubst-eq`) | ○ | Expressible via `wt::perturb_conv`. |
| `05:996` | **Lifting** (`lem:dt:lift`), `i ≤ i'` | ✅ / ○ | `ch05_06_lemmas::typing_is_monotone_in_the_layer` *(new)* covers `p → m`; the `c → p` arm is ○ (needs a layer-`c` generator entry point). |
| `05:1039` | **Unlifting**, `p → c` | ○ | The sharper direction, and unchecked. |
| `05:1055` | **Static Code** (`lem:dt:static`) — at `v`/`c`, `T ≡ T'` ⇒ `T = T'` | ○ | Hand-built instances only: `conv::box_compares_syntactically`, `conv_pair_properties::box_is_intensional`. |
| `05:1075` | **Global Substitutions** preserve typing | ○ | Blocked on a *well-typed* `σ` generator (`gen_sigma` is scope-only). |
| `05:1219` | Presupposition of `σ`-equivalence | ⊘ | |
| `05:1226` | **Equivalent Global Substitutions** (`lem:dt:gsubst-eq`) | ○ | |

### Contexts and presupposition

| Paper | Lemma | Verdict | Kernel counterpart |
|---|---|---|---|
| `05:1277` | **Local Context Equivalence** (`lem:dt:lctxeq1`) | ◐ | `conv::ctx_conversion` (hand-built) |
| `05:1353` | Symmetry and transitivity of local contexts | ○ | `conv_local_ctx` is public; expressible. |
| `05:1365` | **Local Context Conversion** (`lem:dt:lctxeq2`) | ○ | |
| `05:1403` | Presupposition of global-context equivalence | ⊘ | No `Ψ ≈ Φ` judgment in the kernel. |
| `05:1408` | `lem:dt:lctxeq-id` | ○ | |
| `05:1411` | `lem:dt:gctxeq-id` | ⊘ | |
| `05:1420` | **Global Context Equivalence** | ⊘ | |
| `05:1446` | **Presupposition** — `⊢ t : T @ l` ⇒ `⊢ T @ l` | ✅ | `ch05_06_lemmas::inferred_types_are_well_formed` *(new)* |

**`05:1446` in inference mode is the sharp reading.** `infer_term` *produces* a
`(T, l)` pair, and nothing re-read it. That is the same shape of blind spot as
the missing half of Preservation — a judgment the implementation emits and
never checks — which is why it was written first.

### Coverage and Progress of the recursive principles (`sec:dt:syn:cov`)

Thirteen inversion lemmas at layer `c` (`05:1535`, `:1543`, `:1556`, `:1560`,
`:1565`, `:1573`, `:1576`, `:1582`, `:1587`, `:1591`, `:1596`, `:1607`,
`:1622`): four for types, nine for terms, each saying that a well-typed layer-`c`
subject has the indices its β rule needs, as sub-derivations.

**Verdict: ✅ by proxy, for the identity motive.**
`conv_properties::identity_recursor_is_identity_on_code_of_{types,terms}` fires
the recursor on arbitrary generated code and demands the identity back in one
β-step. A coverage failure sticks (no branch fires); a progress failure
mis-fires. `wf_codes.rs` adds the hand-built round-trips for the eight phase-3
branches. What is *not* covered is a motive that genuinely depends on `ℓ` —
which is exactly the configuration the reverted `Unit`-polymorphism fix broke.

This family is also where candidate **(b)** of [[unit-level-and-vec-preservation]]
lives. Its gating question — *does anything require every layer-`p` type at
level `l` to have a code at `Ty l`?* — was checked against the paper while
compiling this audit and **no completeness claim was found**: `Tarski` occurs
five times in ch. 04 (`04:96–120`, `:203`, `:781`), every occurrence describing
the *separation* of types from terms and why Russell-style universes cannot
state the indices of code, never a surjectivity property; and ch. 07's term
relation at `Ty l` (`07:512–514`) is defined by cases on the code whnf, saying
which codes are related, never that every related type is an `El`. That is
evidence, not a verdict — ch. 08's decidability argument is still unread, and
so is the kernel's own "boxed code stays exhaustively recursable" invariant,
which is ours and not the paper's.

---

## What the sweep changed

**Nine new property tests** in `crates/kernel/tests/ch05_06_lemmas.rs`, closing
seven paper lemmas or halves of lemmas. Suite: **312 → 322**.

**One defect found, and it is in the suite rather than the kernel.**
`inferred_types_are_well_formed` failed on its seed 152, first run: a *generated
term that does not type-check*. Every property test in the crate presupposes
that `gen_wt_term` produces well-typed terms, and that presupposition was
checked by exactly one test (`conv_properties::generated_terms_type_check`) at
300 cases on a single seed stream. Measured rate: **1 in 3000**. Three hundred
cases on one stream will essentially never see it.

The defect: `TyPi` binds its global type variable at layer `p`, and the kernel
*fixes* that (`typing.rs:575`), so a `TyPi`-bound `U` may never be named at
layer `c`. The generator built the `Δ` of a contextual type at layer `p` — which
is what ch. 04's rule says — so `Δ` could contain `U^δ`; a layer-`c` body
generated in that `Δ` could then lift the entry type into an annotation (a `J`
motive, in the witness), which is ill-formed at `c`. The kernel was right at
every step.

Fixed by generating every `Δ` that hosts a layer-`c` body at layer `c`
(`common/wt.rs`, nine sites). Such a `Δ` is still a valid layer-`p` context by
ch. 05's Lifting lemma — which `typing_is_monotone_in_the_layer` now checks, so
the fix rests on a machine-checked lemma rather than on an argument. Verified at
15 000 witnesses across three streams, and pinned by
`the_generator_oracle_holds_across_seed_streams` (four streams × 800).

The cost: `Δ`s containing layer-`p`-only types are no longer generated. That is
a real narrowing, and it is the *right* narrowing — those are precisely the `Δ`s
whose entries cannot legally be reused inside code — but a future test that
wants a `p`-only `Δ` will have to build it by hand.

## Ranked remaining gaps

1. **Static Code** (`05:1055`) — at layers `v`/`c`, convertibility *is*
   syntactic identity modulo level equivalence. The most load-bearing open
   gap: it is the property that makes the code eliminator's intensional
   analysis meaningful, and it sits next to the open decision in
   [[unit-level-and-vec-preservation]]. Hand-built instances only.
2. **Unlifting** (`05:1039`) and the `c → p` arm of **Lifting** (`05:996`) —
   needs a layer-`c` generator entry point, which the generator fix above has
   now made routine.
3. **Global Substitutions preserve typing** (`05:1075`) — the largest build
   cost (a well-typed `σ` generator; `gen_sigma` is scope-only) and the largest
   coverage win, since `σ` is the namespace the elaborator will live in.
4. **Reduction under `φ` and `σ`** (`06:280`, `06:298`) — completes the trio
   whose `δ` member is now checked. Cheap once (3) exists.
5. **Equivalent Local Substitutions** (`05:799`) — `perturb_conv` already
   builds the witnesses.
6. **`GlobalSubst::compose`** (`05:377`) — blocked by design, not by effort.
   Decide whether the elaborator needs it *before* adding it, and add the two
   algebra laws in the same change.
7. **Transitivity of convertibility** (`06:721`) — reflexivity and symmetry are
   checked; the third PER law is not.

## The generalization, restated

The `Vec` bug survived three phases because the suite checked one half of a
two-part lemma. This audit found the same shape twice more in one sitting: the
type half of ch. 06's *Soundness* was missing next to the term half, and the
suite's own generator-soundness oracle was a single 300-case stream standing in
for a precondition that ten property tests depend on.

The pattern generalizes past lemmas with halves: **anything the implementation
emits and never re-reads is a blind spot** — an inferred type, a generated
witness, a classification predicate maintained in two places. Three of the nine
new tests are of exactly that kind.
