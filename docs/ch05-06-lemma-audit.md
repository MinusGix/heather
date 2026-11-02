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
| *(ours)* | **Machine adequacy** — `eval` ≡ ch. 06 `⇝*`, both directions | ◐ | **Owed since 2026-07-31**: `conv.rs` is the environment machine, `reduce.rs` is the specification. Tested, not proved — `tests/eval_differential.rs` (head-shape agreement, 5 streams × 600) and `tests/conv_differential.rs` (verdict agreement, 6 streams, both δ modes). See the note below. |
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

**On machine adequacy (the row with no paper location).** The paper has no
such lemma because it has no machine: ch. 06 *is* the algorithm. Until
2026-07-31 `reduce.rs` was conversion's engine as well as ch. 06's
transcription, so there was nothing between specification and implementation
for a lemma to bridge. `docs/nbe-conversion-design.md` put an environment
machine there, and with it **"conversion is ch. 06 verbatim" became
"conversion *decides* ch. 06's relation"**. The gap is exactly this
statement: `eval(t, ρ)` is related to the ch. 06 whnf of `t`
(completeness), and every value `eval` returns is (soundness — the half that
forbids the machine from inventing reductions). The design doc §11.2 states
the relation. Since 2026-09-18 the obligation has one more equation inside
it, because a definition's body is now read as stored rather than rescoped
into the ambient Ψ: `eval(shift_global(k, t), ρ) = eval(t, ρ @ k)`, the body
of `docs/lazy-global-offset-design.md` — a refinement of this row's
obligation, tested where the rest of it is, against the rewriter.

The verdict is **◐, not ✅**, and the distinction is the point. What exists
is *mechanical evidence*, at two levels and deliberately not one: the
evaluator against the rewriter by head-shape agreement recursing through
forcing (`tests/eval_differential.rs`), and the two whole conversions
against each other verdict for verdict (`tests/conv_differential.rs`,
against `conv::oracle`). Both run over `wt.rs`'s well-typed generator
across several seed streams, in both δ modes, with fuel asserted as an
invariant rather than a threshold. That is standing evidence and it found
one real defect (a value-side substitution tail); it is not a proof, and the
row stays ◐ until §11.2's logical relation is actually carried out. Keeping
`reduce.rs` as the specification — it is also still `typing.rs`'s whnf — is
what makes the evidence collectable at all, which is why `conv::oracle`
exists and why deleting it would silently downgrade this row.

Recorded here rather than in `docs/metatheory-ch07-extensions.md` because it
is a ch. 06-level property about an algorithm, not a ch. 07 obligation about
a declarative system — the declarative system does not move.

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
| `05:1055` | **Static Code** (`lem:dt:static`) — at `v`/`c`, `T ≡ T'` ⇒ `T = T'`, *modulo level equivalence* | ✅ | `ch05_06_lemmas::code_equality_is_equality_modulo_level_equivalence` + `::level_equivalent_code_is_convertible` *(new)*. **Found a kernel defect — see below.** |
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
lives; both of its open questions are settled in the next section.

---

## Two questions settled by reading further

The audit above left two things open. Both are now closed by reading ch. 08 in
full and ch. 06's normal-form grammar.

### 1. Nothing requires Tarski completeness. (b) is not blocked.

*Does anything require every layer-`p` type at level `l` to have a code at
`Ty l`?* **No.**

- **ch. 08 in full** (372 lines) proves Injectivity of Type Constructors
  (`08:19`), Consistency (`08:48`), Conversion (`08:96`), Convertibility
  (`08:226`), Decidability (`08:239`) and Decidability of Convertibility
  (`08:357`). Every one is structural induction on derivations. None
  quantifies over "all types at level `l`", and `El` appears only through the
  neutral clause.
- **ch. 07's Neutral Types law** (`07:239`) reads `El l ν ≈ El l' ν'` *given*
  the code relation — a closure rule building related types from related
  codes. It never says every related type is an `El`.
- **ch. 07's Type Constructors law** (`07:220–229`) states `Ty l ≈ Ty l' @ 1+l`
  only when `l ≡ l'`, and `Nat ≈ Nat @ 0` **only at level 0**. These are the
  *laws* both of ch. 08's instantiations must satisfy, and they are where
  non-cumulativity lives semantically.
- **ch. 04's five `Tarski` mentions** (`04:96–120`, `:203`, `:781`) are all
  about the type/term *separation* and why Russell-style universes cannot even
  state the indices of code. Never a surjectivity property.

Two things found on the way that bear on (b) more than the question did:

**A layer-`c` term legitimately has a layer-`p` type.** The paper's
global-context rule (`04:~985`) admits `u : Trm_i(Δ ⊢ T @ l)` for
`i ∈ {v, c}` while requiring only `⊢_p T @ l` — the type is checked at **p**
even for a **c** binding, which `typing.rs:154` matches. Ch. 05's Presupposition
demands `⊢_{typeof(i)}`, and `typeof(c) = p`; the coverage lemmas conclude
their type equivalences at layer `p` too (`05:1573`, `:1576`, …). So the
type-level asymmetry (b) introduces sits exactly in a gap the system already
has, deliberately. **This is a stronger argument for (b) than the one in the
issue** ("§4's argument is entirely about layer `c`"), because it is
structural rather than an appeal to what a paragraph was about.

**The LR never inverts on a level.** The only two "must be unique" appeals in
the logical relations (`07:761`, `07a:1092`) are to determinacy of `⇝*` — the
whnf is unique — not to a type determining its level.

**What (b) actually costs**, now that the metatheory is not the obstacle: it
falsifies `vec_fin::every_type_has_exactly_one_level` and the new
`ch05_06_lemmas::inferred_level_is_the_only_level`, both of which quantify at
layers `p`/`m`. Under (b) both are false **by design** at `p` and would have to
be re-scoped to layer `c`. Downstream, `infer_type` stops being a deterministic
level oracle at `p` for `Unit`/`Empty`, which is a direct input to
[[elab-unifier-completeness]]'s level inference. That is the real trade, and it
is a design cost rather than a soundness one.

### 2. "Boxed code is exhaustively recursable" is wrong as stated — and the paper says so

Ch. 06's neutral-term grammar (`06:31–38`) lists, as **neutral forms**:

```
ν := … | elim_Typ(…; box (U^δ)) | elim_Trm(…; box (u^δ))
```

followed by, verbatim:

> *Notice that for the recursive principles, we block on global variables,
> following [hu2024layered].*

So `box (u^δ)` is well-typed layer-`c` code that **no branch covers**, by
design. The correct invariant is *"exhaustive over the syntactic formers, or
blocked on a global variable"*, and the blocking is part of the normal-form
grammar rather than an implementation shortcut.

Ch. 05's coverage prose is what misled us: it enumerates four type lemmas and
nine term lemmas (`05:1535`–`:1622`) and closes with "There is no other
possible terms at layer `c`" — which is only true of the *syntactic formers*.
Global variables are legal at layer `c` (`i' ≤ i` in both variable rules) and
are simply not in that list, because ch. 06 handles them.

**The kernel was already right**, in both the code and the careful write-up:

- `reduce.rs::is_neutral_term` blocks `ElimCodeTy`/`ElimCodeTm` exactly on
  `box (GlobalTy)` / `box (GlobalTm)`, tested by
  `reduce.rs::recursors_block_on_boxed_global_variables`.
- `docs/metatheory-ch07-extensions.md` §8 already annotates both counts with
  "`GlobalTy` is the blocked/neutral rule, not a branch" and "`GlobalTm` is
  the blocked rule".

What was wrong was the **shorthand** — "so boxed code is still exhaustively
recursable" in `issues/wf-former.md` and `tests/wf_codes.rs`. Corrected in
both, now with the ch. 06 citation, which makes it the paper's design decision
rather than ours.

---

## Static Code (`05:1055`): the sweep's first *kernel* defect

The lemma states that at layers `v`/`c` equivalence is equality, and then adds
the line that matters:

> *All equalities above are quotient over the equivalence of universe levels.*
> … *For example, `Ty (ℓ ⊔ ℓ')` and `Ty (ℓ' ⊔ ℓ)` as code are considered
> **equal**, though their universe levels are not exactly syntactically
> identical.*

`conv.rs` compared boxed code with plain `==` on the syntax, and `Level`
derives `PartialEq` structurally. So the kernel **rejected the paper's own
example, verbatim**: `box (Ty (ℓ ⊔ ℓ'))` and `box (Ty (ℓ' ⊔ ℓ))` both check at
the same `□(· ⊢ Ty (1 + (ℓ ⊔ ℓ')))` and were not convertible.

This is **incompleteness, not unsoundness** — the checker rejected too much,
never accepted too much — but it contradicts ch. 08's Convertibility theorem
(`08:229`: `⊢ T ≡ T' @ l` implies the algorithm accepts), and it would have
surfaced as a spurious error in any universe-polymorphic metaprogram that
built the same code two ways.

**The same shape as the `Vec` bug, one level up.** The implementation read the
lemma's headline (`T = T'`) and not the sentence two lines below it that says
which equality. Half a lemma again — this time half a *sentence*.

Fixed by `Type::normalize_levels` / `Term::normalize_levels` (`subst.rs`),
which rewrites every level to `LevelNf::canonical` (`level.rs`) and reuses the
existing generic traversal rather than adding a third transcription of the
syntax. `conv.rs`'s `code_eq` is `a == b || a.normalized() == b.normalized()`,
so the common case stays allocation-free.

*Later (2026-11-02, `issues/kernel-compact-level.md`):* levels became
canonical by construction, so `normalize_levels` was retired and `code_eq` is
plain `==`. The quotient is now the representation's, not a pass's.

**One thing the test could not pose, which is itself informative.** There is no
pair of codes at *inequivalent levels but the same code type*: `□(Δ ⊢ Ty l)`
fixes `l`, and at layer `c` a type determines its level — that is
uniqueness-of-types, the property [[unit-level-and-vec-preservation]] is about.
So inequivalent levels force inequivalent code types and the two sides never
meet at one `conv_term` call. The level-sensitivity of the comparison is
carried instead by the positive cases being exactly the ≈-classes, bracketed
by two negatives: `box (El Nat)` vs `box Nat` (same level, different syntax),
and `box (Vec(Nat;0))` vs `box Unit` — p-convertible via the open `Vec` gap,
both at level 0, and correctly kept apart as code.

**Consequence for the open decision.** This does *not* settle (a) vs (b) — I
expected it to and it does not. What it does is remove a landmine specific to
**(a)**: level-indexed `Unit^l`/`Empty^l` puts a level into a layer-`c` type
former, so `box (Unit^{ℓ⊔ℓ'})` vs `box (Unit^{ℓ'⊔ℓ})` would have hit exactly
this bug. (a) is now safe to build on that front; (b) leaves layer `c`
untouched and was never exposed to it.

---

## What the sweep changed

**Eleven new property tests** in `crates/kernel/tests/ch05_06_lemmas.rs`,
closing eight paper lemmas or halves of lemmas. Suite: **312 → 324**.

**Two defects found.** The first is in the kernel: boxed code was compared
without the level quotient Static Code takes (previous section). The second is
in the suite:
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

1. **Unlifting** (`05:1039`) and the `c → p` arm of **Lifting** (`05:996`) —
   needs a layer-`c` generator entry point, which the generator fix above has
   now made routine.
2. **Global Substitutions preserve typing** (`05:1075`) — the largest build
   cost (a well-typed `σ` generator; `gen_sigma` is scope-only) and the largest
   coverage win, since `σ` is the namespace the elaborator will live in.
3. **Reduction under `φ` and `σ`** (`06:280`, `06:298`) — completes the trio
   whose `δ` member is now checked. Cheap once (2) exists.
4. **Equivalent Local Substitutions** (`05:799`) — `perturb_conv` already
   builds the witnesses.
5. **`GlobalSubst::compose`** (`05:377`) — blocked by design, not by effort.
   Decide whether the elaborator needs it *before* adding it, and add the two
   algebra laws in the same change.
6. **Transitivity of convertibility** (`06:721`) — reflexivity and symmetry are
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
