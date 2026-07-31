# Ch. 07 pen-and-paper pass for the kernel-v1 extensions

Status: **part I** (§§1–9), the kernel-v1 formers, 2026-07-24. **Part II**
(§§10–17), the `Wf` round, 2026-07-25. Pen and paper, not mechanized.
Tracking issues: `issues/metatheory-ch07-pass.md` (earmarked from
`issues/kernel-v1-extensions.md`); `issues/wf-former.md` phase 4 for part II.

The kernel extends DeLaM ch. 04 with six type formers that the paper's
logical relations (ch. 07/07a/07b) never saw: `Id`, `Σ`, `Unit`, `Empty`,
`+`, `W`. Each landed with its LR obligation earmarked but never checked.
This note walks the obligations and records, per former, whether the
fundamental theorem still goes through.

**Conclusion up front: nothing breaks.** No kernel rule needs changing. The
new work is bookkeeping in four known places, plus one genuinely new
definitional shape (`W`'s infinitary constructor case) and two rules that
the *declarative* side owes us (§7).

---

## 1. What an extension owes ch. 07

A new former that is available at *all* layers — which all six are; they are
MLTT formers, not meta-programming ones — has to appear in five places:

1. **Generic-equivalence laws** (07 §Generic Equivalence): a *Type
   Constructors* clause for the former, a *Congruence* clause per
   constructor, a *Congruence for Neutrals* clause per eliminator. These are
   the laws the two instantiations must satisfy — the declarative
   equivalence of ch. 04, and the conversion algorithm of ch. 06 (i.e.
   `crates/kernel/src/conv.rs`). §6 cross-checks the algorithm.
2. **A Kripke LR case** (07 §sec:dt:klogrel), in the `j = p` block, since
   these are MLTT types: a type-relation rule `D` (whnf on both sides,
   generic equivalence of the whnfs, Kripke-quantified premises for the
   components) plus the term relation `t ~ t' @ D`.
3. **The `j = p` property lemmas** (07 §sec:dt:logrel-prop): weakening,
   escape, reflexivity-of-neutral, weak-head expansion, symmetry, left/right
   irrelevance, reflexivity+transitivity — one new case each.
4. **The layering-restriction lemma** (07a, `j = p` ⇄ `j = m`): one case
   each. This is the lemma that lets a layer-`c`/`p` variable be substituted
   by a layer-`m` term (running code at layer `m`). The cases with a
   *contravariant* premise — where the relation quantifies over related
   inputs — are the ones needing the iff-strengthened IH, as `Π` does.
5. **Fundamental-theorem arms** (07b): one per typing/equivalence rule of
   the former (formation, intro congruences, elim congruence, β, η).

Plus, because our formers are also in the *code* language (layer `c`), the
code recursors get branches, and the recursor arms of the fundamental
theorem (07b §More Semantic Rules) must stay exhaustive — §5.

---

## 2. Positive formers: `Sum`, `Nat`-shaped reasoning

`Sum` is the easy one and sets the pattern for the other positives, so it
goes first even though the issue lists it third.

**LR case.** Exactly `Nat`'s shape (07, `ldtyeqnat`), but with payloads:

- type rule `D`: `T ⇝* A +^{l,l'} B`, `T' ⇝* A' +^{l,l'} B'`, whnfs
  generically equivalent, and Kripke premises `E :: ∀ψ. A ~ A' @ l`,
  `E' :: ∀ψ. B ~ B' @ l'`. Non-dependent, so unlike `Σ`/`W` the second
  premise does *not* quantify over related terms of the first.
- term relation: reduce both to whnf, require generic equivalence, then an
  auxiliary inductive `NfEqSum`: `inl a ~ inl a'` when `a ~ a' @ E(id)`;
  `inr b ~ inr b'` when `b ~ b' @ E'(id)`; `ν ~ ν'` when generically
  equivalent neutrals. Tag mismatch is *not* related — matching
  `conv.rs`'s `(Inl|Inr, _) => NotConvertible`.

**Fundamental theorem, `case` arm.** Induction on `NfEqSum`, precisely the
`elim_Nat` lemma of 07b (lines 1128–1172): the `inl`/`inr` cases use the
branch premise plus reduction expansion, and need the same motive-shuffle
step (`M[δ, t/z] ≈ M[δ, inl a/z]` from `t ≈ inl a` extending `δ ≈ δ`); the
neutral case is reflexivity-of-neutral. There is no recursive premise at
all, so it is strictly *simpler* than `Nat` — no IH inside `NfEqSum`.

**Layering restriction.** No contravariant premise; a direct induction.

`Empty` is the degenerate positive (and **level-indexed** as of §10.3, so read
`Empty^l`): type rule with no component premises,
term relation = "both whnf are generically equivalent neutrals" (no
constructor case, matching `conv.rs`'s `Type::Empty => tm_nee`).
`elim_Empty`'s arm is the neutral case alone. Worth recording as a *gain*:
with `Empty` in the LR, ch. 08's consistency statement is direct — in the
empty local context there are no neutrals, so the term relation at `Empty`
is empty, so `Empty` has no closed inhabitant. Previously that had to be
routed through a `Nat`-based encoding.

`Unit` is the degenerate positive *with η* — see §4.

---

## 3. `Σ` — negative, definitional η

The earmark asked whether the LR at `□(Δ ⊢ Σ … @ l)` is closed under
surjective pairing. It is, but the load-bearing point is a level up: **the
LR case for `Σ` must be the negative (projection) one**, not the pair-shaped
positive one, because `conv.rs` implements η type-directed (`Type::Sigma`
arm: compare `fst a ≈ fst b` and `snd a ≈ snd b`, firing on pairs, neutrals,
or mixtures).

**LR case.**

- type rule `D`: `T ⇝* Σ^{l,l'}(x:S₁).T₁`, `T' ⇝* Σ^{l,l'}(x:S₂).T₂`, whnfs
  generically equivalent, `E :: ∀ψ. S₁ ~ S₂ @ l`, and
  `F :: ∀ψ, ∀ s ~ s' @ E(ψ). T₁[s/x] ~ T₂[s'/x] @ l'` — the same premise
  shape as `Π`.
- term relation: reduce both to whnf, require generic equivalence at both
  types (duplicated, as everywhere, to keep symmetry cheap), then
  `A :: fst w ~ fst w' @ E(ψ)` for all `ψ`, and
  `snd w ~ snd w' @ F(ψ, A)`.

Everything downstream then goes through *without* a case analysis on whether
the whnf is a literal pair:

- **escape** needs the generic equivalence to be closed under η — supplied
  by the declarative surjective-pairing rule (§7) and by `conv.rs`'s η arm;
- **reflexivity of neutral** needs `fst ν`, `snd ν` to be neutral (they are:
  `is_neutral_term` propagates through `Fst`/`Snd`) and generically related
  — supplied by the new *Congruence for Neutrals* laws for `fst`/`snd`;
- **β** (`fst (pair a b) ⇝ a`) is a reduction-expansion step;
- **η** (`p ≈ ⟨fst p, snd p⟩`) is *not* a separate semantic obligation at
  all under the negative reading — both sides have the same projections up
  to β, which is the whole point of choosing it.

`Σ`'s premise `F` is contravariant (it quantifies over related `s`), so its
**layering-restriction** case needs the iff-strengthened IH exactly as `Π`
does (07a lines 1078–1153). Mechanical, but it is not one of the "simpler
than the function case" cases the paper waves through.

**At `□`:** the earmark's actual question. `□(Δ ⊢ Σ… @ l)` is a *code* type;
its LR case (07a §`j = m`) relates `box t₁` only to *itself*, syntactically
(static code lemma), and neutrals to neutrals. η at `Σ` never produces or
consumes a `box`, so it cannot perturb that relation. The inner type of a
`□` is compared up to conversion (LR premise `⊨ᵈ T₁ ≈ T₁'`, and `conv.rs`
`Type::CodeTm` recurses with `self.ty` at layer `p`), so a `Σ` under a `□`
is related up to η *as a type* — which is what we want and is independent of
the term-level question.

---

## 4. `Unit` — η as proof irrelevance

> **Level note (2026-07-25).** `Unit`/`Empty` are now **level-indexed**,
> `Unit^l : Type @ l` — see §10.3. Read every `Unit` below as `Unit^l` with
> the level carried; nothing in this section's argument depended on it being
> `0`, and both rules stay premise-free base cases.

`Unit` has no eliminator; η is definitional and total (`conv.rs`:
`Type::Unit => Ok(())`).

**LR case.** Type rule: both sides reduce to `Unit^l`. Term relation: `t ~ t'`
iff both are well-typed at `Unit` — no whnf condition, no case analysis.
This is the standard irrelevant-unit LR.

The one thing this *costs* is that **escape at `Unit` is not derivable from
the structure of the terms**: it must come straight from a generic-equivalence
law. So η-`Unit` is now a required law of the generic equivalence, which both
instantiations owe (§7). Once it is a law, every property lemma at `Unit` is
trivial (weakening, symmetry, transitivity, irrelevance, reflexivity of
neutral, weak-head expansion all hold vacuously), and layering restriction is
immediate.

Two consequences worth being explicit about, neither a problem:

- **Presupposition is no longer readable off the algorithm.** The `Unit` arm
  returns `Ok(())` without inspecting either side, so it relates ill-typed
  junk too. Ch. 08's laws are stated for well-typed inputs, and the kernel
  only invokes conversion on well-typed input, so the law survives — but it
  survives *by assumption on the caller*, not by the algorithm's structure.
- **Order matters in the algorithm.** η must be tried before the structural
  fallback for completeness (`⟨⟩` vs a neutral). `conv.rs` gets this right:
  the `Type::Unit` arm is in `tm_nf`, dispatched on the type, ahead of any
  `tm_nee` fallback.

---

## 5. `W` — positive, infinitary; the heaviest case

This is the one that needed real thought.

**LR case.**

- type rule `D`: mirrors `Σ`/`Π` — `T ⇝* W^{l,l'}(x:S₁).T₁`, likewise `T'`,
  whnfs generically equivalent, `E :: ∀ψ. S₁ ~ S₂ @ l`, and
  `F :: ∀ψ, ∀ s ~ s' @ E(ψ). T₁[s/x] ~ T₂[s'/x] @ l'`.
- term relation: reduce both to whnf, require generic equivalence, then the
  auxiliary `NfEqW`:
  - `sup(a, f) ~ sup(a', f')` when `a ~ a' @ E(id)` **and** for all
    `ψ :: L' | Φ; Δ ⟶ L | Ψ; Γ` and all `b ~ b' @ F(ψ, …)`, the subtrees
    `f b` and `f' b'` are related by the *outer* term relation at `W`
    (i.e. by `NfEqW` after weak-head reduction);
  - `ν ~ ν'` for generically equivalent neutrals.

`NfEqW` is therefore an **infinitary, Kripke-quantified inductive
definition**: the recursive occurrence sits under `∀ψ. ∀ b ~ b'. …`. It is
strictly positive, so it is a legitimate inductive definition — but it is a
new *shape* in this development. `NfEqNat` recurses finitarily (`su t`), and
`Π`'s quantification lives in the type relation `D` (defined by recursion,
not induction), never inside an inductive term relation. `W` is the first
place where the two are combined. Nothing about the recursion on universe
levels changes: the subtree premise is at the *same* level `l ⊔ l'`, carried
by the inner induction, exactly as `Nat`'s `su` case is carried at level 0.

**Fundamental theorem, `elim_W` arm.** The novel reduction is

```
elim_W(…; sup(a, f))  ⇝  s[a, f, λy. elim_W(…; f y)]
```

— the only β rule in the kernel that synthesizes a λ. The arm is an
induction on `NfEqW`; in the `sup` case we must supply the semantic step
premise with three related arguments, and the third is the synthesized λ.
Showing `λy. elim_W(…; f y) ~ λy. elim_W(…; f' y)` at
`Π^{l',l''}(y : T[a/x]). M[f y/z]` unfolds to the `Π` term relation, i.e.
for all `ψ` and all `b ~ b'`:

```
app(λy. elim_W(…; f y), b)  ⇝  elim_W(…; f b)
app(λy. elim_W(…; f' y), b') ⇝  elim_W(…; f' b')
```

and those two are related by the **inner induction hypothesis of `NfEqW`**,
which is exactly the premise `NfEqW(f b, f' b')` that the `sup` case carries.
Weak-head expansion (07, lemma) closes the gap between the applications and
their reducts, and the generic-equivalence side of the `Π` relation is
discharged by the λ-congruence (η) law. So the arm goes through, and the
reason it goes through is precisely the Kripke `∀ψ` in `NfEqW` — a
non-Kripke formulation would not survive the application under a weakening.
Recording that dependency is the main product of this section.

`conv.rs`'s `Type::W` arm compares subtree functions at the instantiated `Π`
type (hence η-expanded against a fresh variable in an extended context),
which is the `∀ψ` premise instantiated at a weakening plus
reflexivity-of-neutral — the same bridge the `Π` case uses.

**Layering restriction** for `W` has a contravariant premise (`F`, and the
subtree quantifier), so like `Π` and `Σ` it needs the iff-strengthened IH.

---

## 6. `Id` — the original earmark

The worry as filed: `Id` makes code conversion *propositionally observable*
at `□(Δ ⊢ T)` while the recursor is intensional, and the recursor cases of
the LR are where that could bite.

**LR case.** Type rule: `T ⇝* Id^l(S; a; b)`, `T' ⇝* Id^l(S'; a'; b')`,
whnfs generically equivalent, `E :: ∀ψ. S ~ S' @ l`, and `a ~ a' @ E(ψ)`,
`b ~ b' @ E(ψ)`. Term relation: whnf both sides, generic equivalence, then
`NfEqId`: `refl ~ refl` (points related at `E(id)`), and `ν ~ ν'` for
generically equivalent neutrals. **No `refl ~ ν` case** — matching
`conv.rs` (`(Refl, _) => NotConvertible`), i.e. no K/UIP. `J`'s arm is the
`elim_Nat` argument again: `refl` case by β + reduction expansion, neutral
case by reflexivity-of-neutral.

**Does it bite at `□`?** No, and the reason is worth pinning down because it
is a load-bearing invariant rather than an accident:

- `refl^l(S; t)` *synthesizes* `Id^l(S; t; t)` (`typing.rs`), so checking
  `refl` against `Id^l(S; a; b)` goes through **conversion** on the
  endpoints;
- at a code type, conversion is **syntactic identity** (`conv.rs`
  `Type::CodeTy`/`Type::CodeTm` compare `box` payloads with `==`), matching
  the LR's `j = m` case where `box t₁` is related only to itself;
- therefore `Id^0(□(Δ ⊢ T @ l); box t; box t')` is inhabited by `refl`
  **iff `t` and `t'` are syntactically equal code** — the same equality the
  code recursor dispatches on.

So propositional equality at `□` is *exactly* the intensional equality the
recursor observes, not a coarser one. There is no rule in the other
direction: `J` eliminates an `Id` into a motive, it never produces a
definitional equality, and there is no unbox congruence. The recursor arms
of the LR are unaffected — they case-analyse the *syntax* of boxed code and
never consult the `Id` relation.

The strengthening this relies on: **`refl`'s endpoints are compared by
conversion, and conversion at `□` is `==`.** If either half were relaxed
(e.g. a future "conversion up to β for code" convenience, or an
irrelevant/definitional-`Id` rule), the observation and the equality would
part company and this argument would need redoing. Flagged for
`crates/kernel/DESIGN.md` as an invariant, not just an implementation
detail.

### Funext leak audit (grep-level, done alongside)

Claim to confirm: no rule anywhere derives `□`-level equality from
term-level `Id`; funext must stay propositional-only, never a `□`
congruence.

- Every path to relating two `box`es in `conv.rs` is the `==` arm at
  `Type::CodeTy` / `Type::CodeTm` (lines 544–557) and the two `box`-scrutinee
  arms of the recursor bundle (lines 1263–1313, likewise `==`). Nothing else
  concludes `box _ ≈ box _`.
- `letbox` does not unbox into an equation: its β substitutes the code for a
  *global variable*, a global substitution, and global substitutions carry
  syntactically-identical code on both sides in the LR.
- `Id`/`J`/`refl` appear nowhere in the code-comparison paths; the code
  recursor's `tm_id`/`tm_refl`/`tm_j` branches *destructure* code of `Id`,
  they do not equate anything.
- Conversion is only ever invoked at computing layers (`debug_assert!` in
  `conv_type`/`conv_term`), so there is no convertibility judgment at layer
  `c` at all for a leak to travel through.

No leak.

---

## 7. Cross-check: the new laws vs. the algorithm

The generic-equivalence laws are the interface the LR needs and the
conversion algorithm must supply (second instantiation). New laws required,
and where `conv.rs` discharges each:

| new law | kind | `conv.rs` |
|---|---|---|
| `Id`, `Σ`, `Unit`, `Empty`, `+`, `W` type congruences | Type Constructors | `ty_nf` arms (lines 276–319) |
| same six as term *encodings* (`TmId`, `TmSigma`, …) | Type Constructors | `tm_nf` at `Ty l` (lines 593–630) |
| `refl` congruence | Congruence | `Type::Id` arm |
| `pair` congruence *(subsumed by η)* | Congruence | `Type::Sigma` η arm |
| `⟨⟩` / η-`Unit` (any two terms at `Unit`) | Congruence | `Type::Unit => Ok(())` |
| `inl` / `inr` congruences | Congruence | `Type::Sum` arm |
| `sup` congruence | Congruence | `Type::W` arm |
| `J` neutral congruence | Congruence for Neutrals | `tm_ne` (lines 1004–1063) |
| `fst` / `snd` neutral congruences | Congruence for Neutrals | `tm_ne` (lines 1082+) |
| `elim_Empty` neutral congruence | Congruence for Neutrals | `tm_ne` (lines 817–831) |
| `case` neutral congruence | Congruence for Neutrals | `tm_ne` (lines 832–906) |
| `elim_W` neutral congruence | Congruence for Neutrals | `tm_ne` (lines 907–1003) |

All present, and each neutral congruence compares motives and branches at
their *instantiated* types (the ch. 04 telescopes) and the scrutinee via
`tm_nee` — the shape the laws demand.

**What the declarative side owes.** The laws are also owed by the *first*
instantiation, ch. 04's syntactic equivalence, which we do not implement (the
kernel has only the algorithm). Two of them are not mere congruences and
have to be stated as rules on the paper side:

1. **Σ η / surjective pairing**: `Γ ⊢ p ≈ ⟨fst p, snd p⟩ : Σ(x:S).T @ l⊔l'`.
2. **Unit η**: `Γ ⊢ t ≈ t' : Unit @ 0` for any well-typed `t, t'`.

Without these two rules on the declarative side, escape from the `Σ` and
`Unit` LR cases fails and the soundness direction of ch. 08 has nothing to
land on. They are the only genuinely *new rules* (as opposed to congruences)
this extension pass adds.

---

## 8. Code-recursor exhaustiveness

The recursor arms of 07b (§More Semantic Rules) case-analyse boxed code by
syntactic former. That argument is only valid if the branch bundle is
exhaustive over well-typed layer-`c` syntax. Counted against `term.rs`
(**recounted 2026-07-25** for the `Wf` round; the part-I count was 37):

- **Type formers at layer `c`**: `Nat`, `Π`, `Ty`, `El`, `Id`, `Σ`, `Unit`,
  `Empty`, `+`, `W`, `Vec`, `Fin`, `Wf` = 13, matched by `ty_nat`, `ty_pi`,
  `ty_ty`, `ty_el`, `ty_id`, `ty_sigma`, `ty_unit`, `ty_empty`, `ty_sum`,
  `ty_w`, `ty_vec`, `ty_fin`, `ty_wf` = 13.
  (`GlobalTy` is the blocked/neutral rule, not a branch.)
- **Term formers at layer `c`**: `Var`, `TmNat`, `TmPi`, `TmTy`, `TmId`,
  `TmSigma`, `TmUnit`, `TmEmpty`, `TmSum`, `TmW`, `TmVec`, `TmFin`, `TmWf`,
  `Zero`, `Succ`, `ElimNat`, `Refl`, `J`, `Pair`, `Fst`, `Snd`, `Triv`,
  `ElimEmpty`, `Inl`, `Inr`, `Case`, `Sup`, `ElimW`, `Supf`, `ElimWf`,
  `Lam`, `App` = 32, matched one-for-one by the 32 `tm_*` branches.
  (`GlobalTm` is the blocked rule.)

13 + 32 = 45, the bundle `conv.rs` documents (`term.rs` carries exactly 45
`ty_*`/`tm_*` branch fields besides the two motives; `BRANCH_DIMS` in
`crates/kernel/tests/common/mod.rs` agrees). Exhaustive; the recursor arms
have no gap.

**The two parenthesised blocking notes are the paper's design, not ours**
(confirmed 2026-07-25, and worth the citation because the shorthand "boxed
code is exhaustively recursable" elsewhere in the repo overstated it).
Ch. 06's neutral-term grammar (`06_reduction_and_convertibility.tex:31–38`)
lists `elim_Typ(…; box (U^δ))` and `elim_Trm(…; box (u^δ))` among the neutral
forms `ν`, and says outright: *"Notice that for the recursive principles, we
block on global variables, following [hu2024layered]."* Global variables are
legal at layer `c` (`i' ≤ i` in both variable rules), so exhaustiveness is
over the **syntactic formers**, with global variables handled by the
normal-form grammar. Ch. 05's coverage prose (`05:1535`–`:1622`, closing with
"There is no other possible terms at layer `c`") enumerates only the formers
and is what makes the stronger reading tempting.
`reduce.rs::recursors_block_on_boxed_global_variables` pins the kernel's side.

---

## 9. Summary

| former | LR case shape | new definitional risk | layering restriction | verdict |
|---|---|---|---|---|
| `Sum` | positive, `Nat`-shaped, two payload cases | none | direct | goes through |
| `Empty` | positive, neutral-only | none | direct | goes through; gives consistency directly |
| `Unit` | irrelevant (no whnf condition) | escape depends on a *law*, not structure | direct | goes through; owes a declarative η rule |
| `Σ` | negative (projections), `Π`-shaped premises | none | contravariant — iff-IH like `Π` | goes through; owes a declarative η rule |
| `Id` | positive, `refl`/neutral, no K | none | direct | goes through; `□` intensionality confirmed sound |
| `W` | positive, **infinitary Kripke induction** | new inductive shape; `elim_W` β synthesizes a λ | contravariant — iff-IH like `Π` | goes through, via the `∀ψ` premise |

No kernel-rule consequences to file. Two declarative-side rules (§7) are
recorded here rather than as separate issues, since we do not implement the
declarative equivalence; they belong in whatever writeup of the extended
ch. 04 rules we produce. One invariant is worth promoting into
`crates/kernel/DESIGN.md`: *`refl` types by conversion on its endpoints, and
conversion at code types is syntactic identity — together these are what
keep propositional equality at `□` exactly as fine as the recursor's
observation.*

Part II adds three rows to this table; see §17.

---
---

# Part II — the `Wf` round

Status: pen-and-paper pass, 2026-07-25, for the three formers of
`docs/wf-former-design.md`: `Vec`, `Fin`, `Wf` (with `sup_f`/`elim_Wf`).
This is phase 4 of `issues/wf-former.md`, and it is the round that carried
the **abort criterion**: if the `Wf` case of the logical relations needed a
genuinely new idea rather than a finitary restriction of `W`'s, the
branching-inductives decision was to be reopened with route A (`W` + funext)
as the considered fallback.

**Verdict up front: the criterion is not triggered, and the decision
stands.** The `Wf` case is a restriction of `W`'s in a precise sense (§11,
§12) — so precise that the metatheory's own induction requirement drops from
`W`-shaped to `Wf`-shaped. It costs exactly one new lemma (§13), whose four
cases are all reductions the kernel already performs. `Vec` and `Fin` cost
*no new LR case at all* (§10).

The round was not free of findings, though. Writing the fundamental-theorem
arm for `Vec`-formation turned up a **real kernel defect** — type-level
preservation fails across `Vec^l(T;0) ⇝ Unit` for every `l ≠ 0` (§10.3).
That is the pass paying for itself. It is *not* fixed here: the one-line
repair was tried and reverted, because it breaks uniqueness of types at `□`
and with it the code recursor. It is tracked, pinned by tests, and costed in
`issues/unit-level-and-vec-preservation.md`. §10.3 also explains why it
leaves §§11–17 untouched.

---

## 10. `Vec` and `Fin`: no new LR case, and one kernel finding

### 10.1 Neither former gets a type-relation rule

Every type-relation rule of 07 §sec:dt:klogrel is keyed on the **weak head
normal form** of the two types: each premise set begins `T ⇝* W @ l`. So a
former contributes a rule only if it can *be* a whnf. `Vec` and `Fin` are
whnf exactly when their length is stuck (`reduce.rs:1791`, keyed through
`is_neutral_term(len)`), and there they are **neutral** types
(`reduce.rs:1778`). Therefore:

- **canonical length** — `Vec^l(T;0) ⇝ Unit^l`, `Vec^l(T;su k) ⇝ Σ^{l,l}(_:T).
  Vec^l(T;k)`, `Fin(0) ⇝ Empty^0`, `Fin(su k) ⇝ Unit^0 +^{0,0} Fin(k)`. The
  reduction is absorbed by the `⇝*` premise and the existing `Unit`, `Σ`,
  `Empty`, `+` rules apply unchanged. Weak-head expansion (07,
  §sec:dt:logrel-prop) is what carries this: the LR is closed under
  expansion, so `Vec` *inherits* its reduct's clause rather than restricting
  it.
- **neutral length** — the existing **neutral-type** rule applies verbatim,
  with `V = Vec^l(T;ν)`, discharged by the generic neutral-type equivalence
  `lttypgneeq`.

This is the strongest form of the design doc §8 prediction, and it is worth
being explicit that it is stronger: §8 expected "clauses that restrict
`Unit`/`Σ`/`Empty`/`+`'s". There are no clauses. The two formers are, on the
semantic side, entirely invisible.

One small lemma is owed for the neutral case, because the neutral-type rule
relates only *neutral* terms and we must know nothing canonical inhabits a
stuck `Vec`/`Fin`:

> **Canonicity at a stuck length.** If `⊢ t : Vec^l(T;ν) @ l` with `ν`
> neutral and `t` in whnf, then `t` is neutral. Likewise for `Fin(ν)`.

Immediate from the kernel's introduction rules being type-directed on a
*reduced* type: `⟨⟩` checks only at `Unit`, `⟨_,_⟩` only at `Σ`, `inl`/`inr`
only at `+`, and none of these unify with a `Vec`/`Fin` whose length is
stuck. `conv.rs:828–831` is the algorithmic side of the same fact — those
types fall straight through to `tm_nee`.

### 10.2 What they owe the generic equivalence

Two **Congruence for Neutrals** laws, at the *type* level:

```
T ≈ T' @ l      ν ≈ ν' : Nat @ 0                ν ≈ ν' : Nat @ 0
───────────────────────────────── (ν, ν' ne)    ──────────────── (ν, ν' ne)
Vec^l(T;ν) ≈ Vec^l(T';ν') @ l                   Fin(ν) ≈ Fin(ν') @ 0
```

discharged by `conv.rs:313–323`. These are a **new kind** of law for this
development, and it is worth naming why: the neutral-type equivalence has
until now compared neutral types whose components are *terms* (`El ν`'s
premise is `ν ≈ ν' : Ty l`) or nothing at all (`U^δ`). `Vec` is the first
neutral type with a genuine **type** premise alongside a term one. It is
still a legitimately *neutral* relation, because neutrality is decided by
the length alone and the element is simply carried; but the generic
equivalence interface has to be stated as closed under "a former applied to
a related type and a related stuck term", not just "a former applied to
related terms".

The declarative side additionally owes the four computation rules above.
Those are ordinary reductions, not new *shapes* — unlike part I's two η
rules (§7), nothing here is a genuinely new rule.

### 10.3 The finding: `Vec^l(T;0) ⇝ Unit` dropped a level

Writing the fundamental-theorem arm for `Vec`-formation is what exposed
this. The arm must conclude `⊨ Vec^l(T;k) @ l`. At `k ⇝* 0` that unfolds,
via weak-head expansion, to a demand for `Unit ~ Unit @ l`. But the `Unit`
type-relation rule as stated in §4 — and the kernel's `Unit`-formation rule
as implemented — lives at level `0`, and the LR's level-conversion rule
(07, the "bureaucratic" case) requires `l ≈ l'`, level *equivalence*, not
`≤`. So for `l ≠ 0` the arm had nothing to land on.

That is not merely a gap in the paper argument. It is a defect in the
kernel, and a checkable one:

```
⊢ Π^{1,0}(_ : Vec^1(Ty 0; 0)). Nat @ 1        well-formed
  ⇝  Π^{1,0}(_ : Unit). Nat                   LevelMismatch
```

**Type-level subject reduction failed.** `Vec` is the kernel's first type
former whose whnf is chosen by a *term*; `El` is chosen by a term too, but
its term is a code that carries its own level, so `El` cannot drop one.
`Vec`'s length is a bare `Nat`, and at `0` the reduct `Unit` has nothing to
do with `l`. Nothing caught it because the shape of a generated datatype is
a sum of records at level `0`, so every existing test and every prototype
sits at `l = 0`, where `Unit`'s level is right by accident.

This is the exact type half of **DeLaM ch. 06, Lemma *Preservation***: *if
`⊢_i T @ l` and `T ⇝ T'` then `⊢_i T' @ l`*, at the same `l`. The lemma is
not optional bookkeeping — ch. 07's auxiliary judgment `\ttypreds i T W l`
is *defined* as `⊢ T @ l` together with `T ⇝* W`, so every type rule of the
LR carries `l` across the reduction and reads the whnf at that same `l`.

**Status: CLOSED, 2026-07-25, and the obvious fix really was wrong.** The
route taken, its rules and the costed record of what was not taken:
`docs/unit-empty-level-indexing.md`. Tracked in
`issues/unit-level-and-vec-preservation.md`.

The wrong fix, kept because it is the instructive part: making `Unit`/`Empty`
level-**polymorphic** in formation repairs preservation in one line, and was
landed and then reverted in the same session. DeLaM ch. 04 §Non-cumulativity
makes **unique types load-bearing for the code eliminator** — "we must specify
in each case how do we construct the original code from its components;
therefore, it is the most convenient, when each term has a unique type".
`box T : □(Δ ⊢ Ty l)` is checking-only and checks `T` at `l`, so a type that
checks at many levels is a *term* with many types. Measured: with the
polymorphic version in place, `box Unit` inhabits `CodeTy(l)` for every `l`
(`box Nat` correctly does not), and `elim_CodeTy(code_level = 1; box Unit)`
typechecks while firing into the `ty_unit` branch, which `rec.rs` built with
`univs: 0` and instantiated at `ℓ := 0` — so the redex is typed at `M[1/ℓ]`
and the reduct verified at `M[0/ℓ]`. Preservation moves from `Vec` to the code
recursor, which is the worse place for it to be.

The fix that landed is **level-indexed** `Unit^l`/`Empty^l` — parameterized,
not polymorphic, as non-cumulative systems do it. `Vec^l(T;0) ⇝ Unit^l`,
uniqueness of types is preserved on the nose, and `ty_unit`/`ty_empty` became
copies of `ty_ty`, which binds a universe precisely because `Ty ℓ`'s level
varies. It also closed a **functional hole** that the level drop had left and
that this section did not originally notice: `Vec^l(child;0)` is the children
type of a *nullary constructor* of a `Wf` whose shape sits at level `l`, and
`Triv : Vec^1(Ty 0;0) @ 1` was a `LevelMismatch` — so `Leaf` could not be
built for any polymorphic branching inductive. `wf.rs::polymorphic_shape` is
the end-to-end acceptance test.

What this section can still claim unconditionally:

- **`Fin` is unaffected.** Declared at `0`, both reducts (`Empty^0`,
  `Unit^0 +^{0,0} Fin k`) land at `0`. The asymmetry is real and is why `Vec`,
  not `Fin`, exposed this.
- **The successor case is exact.** `Vec^l(T;su k) ⇝ Σ^{l,l}(…)` at `l ⊔ l`.
  The nullary case was the only one at issue.
- **Nothing large ever entered a small universe.** `Vec` only ever
  over-declared, so this was a broken lemma rather than a soundness hole.

**Consequence for §§11–17 below: none**, as predicted. The `Wf` case does not
go through `Vec`'s nullary reduct — `NfEqWf`'s spine bottoms out in the `Unit`
clause at whatever level the repair settled on, and the abort criterion turns
on the *shape* of the recursion. The verdict in §17 stands.

**Consequence for the `Unit`/`Empty` LR rules: they are level-indexed**, which
is what §4 and §2 should now be read as saying. The type rule is
`T ⇝* Unit^l`, `T' ⇝* Unit^l` ⟹ `T ~ T' @ l`, and likewise for `Empty^l` —
cleaner than either the old level-0 rule or the polymorphic one, because the
level is *carried* rather than quantified. Both remain premise-free base
cases, so the well-founded recursion on universe levels never descends
through them and every property lemma at `Unit`/`Empty` stays vacuous
(§2, §4). Nothing in §§2–4's arguments depends on the level being `0`; they
were written before the indexing and survive it unchanged.

### 10.4 The deeper finding: a missing property, not a missing case

`conv_properties.rs` had `reduction_preserves_type` — the **term** half of
ch. 06's lemma — and no type half. That is why this survived from phase 1.
The generator was producing the witness all along: `gen_wt_type` takes
`Vec`'s level from its element and picks a small literal length two times in
three, so `Vec^{l>0}(T;0)` is routine output. Hundreds of witnesses per run,
and nothing looked at them.

`type_reduction_preserves_level` now exists and fails on **seed 102**, first
run, no tuning. The general lesson is worth more than the bug: *half of a
stated lemma leaves a blind spot shaped exactly like its other half.*

**Swept**: `docs/ch05-06-lemma-audit.md` — all 53 lemmas of ch. 05/06, each
with a verdict. It found the same shape twice more (the *type* half of ch. 06
Soundness, `06:148`, one lemma earlier in the same chapter; and the suite's
own generator-soundness oracle running on a single 300-case stream), plus a
kernel defect at ch. 05's Static Code (`05:1055`) where boxed code was
compared without the level quotient the lemma takes.

And the lesson generalized once more during the repair: the well-typed
generator produced **no `Unit`/`Empty` at all**, so the level-indexing round
would have been covered only by hand-built tests. It is not enough for the
observer to exist — the *witness* has to be generated, and that now has its
own assertion
(`vec_fin::the_well_typed_generator_reaches_unit_at_a_nonzero_level`).

---

## 11. `Wf` — the type relation, and the one substitution that makes it finitary

```
D :: ─────────────────────────────────────────────────────────────
     T  ⇝* Wf^l(x:S₁).n₁ @ l        T' ⇝* Wf^l(x:S₂).n₂ @ l
     (components well-formed, as in the Π rule)
     Wf^l(x:S₁).n₁ ≈g Wf^l(x:S₂).n₂ @ l
     E :: ∀ψ. S₁ ~ S₂ @ l
     N :: ∀ψ, ∀ A :: s ~ s' @ E(ψ).  n₁[s/x] ~ n₂[s'/x] : Nat @ 0
     ─────────────────────────────────────────────────────────────
     T ~ T' @ l
```

Set this beside `W`'s rule (§5). `E` is identical. `W`'s second premise is

```
F :: ∀ψ, ∀ s ~ s' @ E(ψ).  T₁[s/x] ~ T₂[s'/x] @ l'     (a TYPE relation)
```

and `Wf`'s `N` is the same premise with a **term relation at `Nat`** in place
of the type relation. That single substitution is the whole difference, and
it is also, in one line, the reason the term relation below is finitary:

> `F` is something the term relation **quantifies over** — contravariantly,
> and over an unbounded domain. `N` is something the term relation
> **recurses on** — covariantly, and `NfEqNat` derivations are well-founded.

Two smaller notes:

- **No new premise kind.** A term relation already appears in the premises
  of type rules (`Π`, `Σ`, `W` all quantify over `s ~ s'`), so `N` is not a
  new shape; it uses one in *positive* position, which is strictly easier.
  Well-foundedness is unaffected: the `Nat` type relation is the
  premise-free base rule of 07, so `N` does not refer back to `D`.
- **Levels get shallower, not deeper.** `W` lives at `l ⊔ l'`; `Wf` lives at
  `l` alone, because an arity is a `Nat` term and contributes no level. The
  transfinite recursion on universe levels has strictly less to do here.

---

## 12. `NfEqWf` — the term relation

```
    t ⇝* w @ Wf₁      t' ⇝* w' @ Wf₂
    w ≈g w' @ Wf₁     w ≈g w' @ Wf₂      (duplicated, as everywhere,
    NfEqWf(w, w')                         to keep symmetry cheap)
    ─────────────────────────────────
    t ~ t' @ D
```

with the auxiliary inductive `NfEqWf`:

```
  A :: a ~ a' @ E(id)
  C :: ∀ψ.  cs ~ cs' @ Vecrel(ψ)
  ─────────────────────────────────────────────────  (sup_f)
  NfEqWf( sup_f(a; cs), sup_f(a'; cs') )

  ν ≈g ν' neutral at both types
  ─────────────────────────────                      (ne)
  NfEqWf(ν, ν')
```

`Vecrel(ψ)` is **not a new relation**. It is the existing term relation at
the pair of types `Vec^l(Wf₁; n₁[a/x])` and `Vec^l(Wf₂; n₂[a'/x])`, whose
derivation is constructed by recursion on the `NfEqNat` derivation that
`N(ψ, A(ψ))` supplies:

| `NfEqNat` case | `Vec` reduces to | clause used | recursive `NfEqWf` premises |
|---|---|---|---|
| `ze / ze` | `Unit` | §4, irrelevant | **0** |
| `su k / su k'` with `K :: k ~ k'` | `Σ^{l,l}(_ : Wf). Vec(Wf;k)` | §3, negative | **1** (`fst cs ~ fst cs'`), then recurse on `K` for `snd` |
| `ν / ν'` neutral | itself, a neutral type | §10.1 | **0** |

So a node carries exactly as many recursive premises as its arity's whnf is
a numeral, and none at all at a neutral arity. `NfEqWf` is a **finitary,
strictly positive, Kripke inductive definition**.

Three points that are load-bearing rather than decorative:

1. **The spine recursion is on the `NfEqNat` derivation, not on either
   length.** The two sides' arities are only *related*, not equal —
   `n₁[a/x]` versus `n₂[a'/x]` — so neither is available to recurse on.
   `NfEqNat` is precisely what forces them to reduce in lockstep (both to
   `ze`, both to `su`, or both neutral), and recursing on it is what makes
   the two `Vec` unfoldings track each other. This is the one technical
   point where a careless transcription of `W`'s clause would go wrong.
2. **`C` must stay Kripke-quantified.** Not for the definition — the finite
   spine needs no `∀ψ` — but for §13 and §14, which apply the children
   relation under a weakening. This is the same dependency §5 recorded for
   `W`, and it survives the restriction unchanged.
3. **The children premise is the *negative* `Σ` reading.** Because §3 chose
   projections over pairs, `C` is `fst cs ~ fst cs'` and `snd cs ~ snd cs'`
   with no case analysis on whether `cs` is a literal tuple. That is the
   semantic counterpart of `sigma_eta_bridges_the_constructor_form`: the gap
   route A bridges with funext is closed inside the `Σ` clause, and `Wf`
   itself never sees it. **`NfEqWf` has no η clause**, exactly as the design
   promised.

**The shape of the result.** `NfEqW` is a `W`-shaped inductive definition in
the metatheory: its recursive premise sits under `∀ψ. ∀ b ~ b'. …`, a
quantification over a *type* of positions. `NfEqWf` is a `Wf`-shaped one:
finitely many recursive premises, the number computed from the node's own
data. The restriction the design argued for at the object level turns out to
hold at the meta level too — a mechanization of this development would need
only finitary branching induction where `W` needs infinitary. That is a
better outcome than "easier, not harder"; it is the same reduction, one
level up.

---

## 13. The index lemma — the price of finitarity

`W`'s `elim_W` arm can read its recursive premise straight out of `NfEqW`,
because `NfEqW`'s premise is *already* in the `∀ψ ∀ b ~ b'` form the arm
needs. `Wf`'s arm cannot: `NfEqWf` stores a finite Σ-spine, and the arm
needs a statement about arbitrary related `Fin` indices. Bridging the two is
the one genuinely new obligation of this round.

> **Lemma (positions).** Let `NfEqWf(sup_f(a;cs), sup_f(a';cs'))` with
> premises `A`, `C`. Then for every `ψ` and every
> `I :: i ~ i' @ Fin(n₁[a/x])`,
> ```
> nth(Wf₁; n₁[a/x]; cs; i)  ~  nth(Wf₂; n₂[a'/x]; cs'; i')   @ D(ψ)
> ```
> and moreover the relation is witnessed by a **subderivation** of the given
> `NfEqWf` whenever both sides are `sup_f`s.

*Proof.* Induction on the `NfEqNat` derivation of
`n₁[a/x] ~ n₂[a'/x]` obtained from `N(ψ, A(ψ))`. Recall `nth` is a fixed
`elim_Nat` schema (`term::nth`, design doc §3), so every reduction quoted
below is one the kernel already performs.

- **arity `ze`.** `Fin(0) ⇝ Empty`, whose term relation (§2) relates only
  neutrals, so `i`, `i'` are neutral; `nth(T;0;cs;i) ⇝ elim_Empty(_.T; i)`,
  neutral. Reflexivity-of-neutral closes it. In the empty local context
  there are no such `i` at all and the clause is vacuous — the `Empty` gain
  of §2, reused.
- **arity `su k`, with `K :: k ~ k'`.** `Fin(su k) ⇝ Unit +^{0,0} Fin(k)`,
  so `I` is an `NfEqSum` derivation (§2):
  - `inl / inl` — `nth ⇝ fst cs` and `nth ⇝ fst cs'`; related by `C`'s first
    component. Weak-head expansion closes the gap to the unreduced `nth`s.
  - `inr j / inr j'` with `J :: j ~ j' @ Fin(k)` — `nth ⇝ nth(T;k;snd cs;j)`
    and symmetrically; apply the induction hypothesis at `K`, with `C`'s
    second component as the children premise.
  - `ν / ν'` neutral — `nth` whnfs to a neutral `case`; reflexivity-of-
    neutral, whose motive and branch premises come from escape on `C`.
- **arity neutral.** `Fin(ν)` is a neutral type (§10.1), so `i`, `i'` are
  neutral and `nth` is a neutral `elim_Nat` under two applications.
  Reflexivity-of-neutral. ∎

Every step runs at an arbitrary `ψ` because `C` is Kripke-quantified; that
is the dependency §12(2) flagged, discharged here.

Four cases, all mechanical, no new definitional shape. This is the entire
cost of choosing the finitary `NfEqWf` over a verbatim transcription of
`W`'s infinitary clause — and it buys the reduction in §12's last paragraph.

---

## 14. Fundamental theorem: the `elim_Wf` arm

The reduction (design doc §4), the second β rule in the kernel that
synthesizes a binder:

```
elim_Wf(x:S.n; z.M; a cs ih. s; sup_f(_; a₀; cs₀))
  ⇝ s[ a₀, cs₀,
       λ(i : Fin n[a₀/x]). elim_Wf(x:S.n; z.M; a cs ih. s;
                                    nth(Wf; n[a₀/x]; cs₀; i)) ]
```

The arm is an induction on `NfEqWf`.

- **neutral case.** Reflexivity-of-neutral, with the `elim_Wf` neutral
  congruence law (`conv.rs:1096–1139`) supplying the generic-equivalence
  side. `elim_Wf` is neutral on a neutral scrutinee (`reduce.rs:1827`).
- **`sup_f` case.** The semantic step premise must be supplied with three
  related arguments:
  1. `a₀ ~ a₀'` — premise `A`.
  2. `cs₀ ~ cs₀'` at `Vec^l(Wf; n[a₀/x])` — premise `C` at `id`.
  3. the two ih λs, related at `Π^{0,l'}(i : Fin n[a₀/x]). M[nth(…)/z]`.
     Unfolding the `Π` term relation: for all `ψ` and all `i ~ i'` at the
     domain,
     ```
     app(λi. elim_Wf(…; nth(cs₀;i)),  i )  ⇝ elim_Wf(…; nth(cs₀;i))
     app(λi. elim_Wf(…; nth(cs₀';i)), i')  ⇝ elim_Wf(…; nth(cs₀';i'))
     ```
     and by the **index lemma** (§13) the two scrutinees are related by a
     *subderivation* of the `NfEqWf` we are inducting on — so the inner
     induction hypothesis applies to the two `elim_Wf`s directly. Weak-head
     expansion closes the gap to the applications; the λ-congruence law
     supplies the generic-equivalence side.

  Then the usual motive-shuffle (`M[δ, t/z] ≈ M[δ, sup_f(a₀;cs₀)/z]` from
  `t ≈ sup_f(a₀;cs₀)` extending `δ ≈ δ`), as in every eliminator arm since
  §2. ∎

Compared with §5's `elim_W` arm, the *only* difference is that the recursive
premise arrives through §13 instead of being read off the `NfEqW` premise.
Everything else — the synthesized λ, the `Π`-unfolding, the reliance on the
Kripke `∀ψ` — is identical.

Two things worth recording, because they are what the design was betting on:

- **No funext obligation appears anywhere in this arm.** The only `Π` in
  sight is the ih, and the `Π` term relation is the *applied* form, so the
  ih is only ever eliminated, never compared as a function. That is the
  semantic counterpart of the design's "the ih is transient" (§4 of the
  design doc, wrinkle 6.2) — conversion showed it, and the LR agrees.
- **The ih's domain reduces.** `Fin n[a₀/x]` is not a whnf at a canonical
  arity, so the `Π` rule's domain premise is discharged by `Empty`'s or
  `+`'s clause, never by a new one. §10.1 again.

---

## 15. Property lemmas and layering restriction

**`Vec`, `Fin`: nothing.** No type-relation case means no case in weakening,
escape, reflexivity-of-neutral, weak-head expansion, symmetry, left/right
irrelevance, reflexivity or transitivity, and none in the layering
restriction. Their reducts' cases discharge all of it, and closure under
weak-head expansion is what makes that legitimate.

**`Wf`: one case each, all by induction on `NfEqWf`.**

| lemma | how |
|---|---|
| weakening | `C` is already `∀ψ`; `A` by IH |
| escape | `NfEqWf` carries `w ≈g w'` at *both* types directly |
| reflexivity of neutral | the `(ne)` rule |
| weak-head expansion | the outer rule reduces both sides first |
| symmetry | `NfEqNat` is symmetric, so the spine recursion mirrors; the duplicated `≈g` premises do the rest |
| left/right irrelevance | as `W`'s |
| reflexivity + transitivity | nested induction; see the note below |

The transitivity case is the one place the spine recursion reappears and is
worth flagging rather than waving through. Composing
`NfEqWf(t₁,t₂)` with `NfEqWf(t₂,t₃)` at the `sup_f` rule needs
`cs₁ ~ cs₃` from `cs₁ ~ cs₂` and `cs₂ ~ cs₃` at three *pairwise related but
distinct* `Vec` types. The arity derivations compose by `NfEqNat`
transitivity, and the spine composition is then a second induction on the
composite `NfEqNat` derivation, mirroring §12's construction. Mechanical,
but it is the second appearance of that recursion and a mechanization would
want it factored out as a lemma about `Vecrel` rather than inlined twice.

**Layering restriction (07a, `j = p` ⇄ `j = m`).** `Wf`'s type rule has a
contravariant premise — `N` quantifies over related `s ~ s'`, exactly as
`Π`/`Σ`/`W`'s `F` does — so this case needs the **iff-strengthened IH**,
like `W`. The children premise `C` is covariant and needs no strengthening.

That is a strict improvement on `W`, and worth stating as such: `W` has
*two* contravariant premises (the position-type premise `F`, and the subtree
quantifier inside `NfEqW`), `Wf` has one. The subtree quantifier is exactly
what §12 replaced with a finite spine.

---

## 16. Cross-check: the new laws vs. the algorithm

Extending §7's table. All present in `conv.rs`; the neutral congruences
compare motives and branches at their instantiated (ch. 04) telescopes and
the scrutinee via `tm_nee`, as the laws demand.

| new law | kind | `conv.rs` |
|---|---|---|
| `Wf` type congruence (arity compared under the shape binder) | Type Constructors | `ty_nf`, 326–334 |
| `Vec` / `Fin` neutral-type congruences | Congruence for Neutrals **(types)** | `ty_nf`, 313–323 |
| `TmVec` / `TmFin` / `TmWf` as term encodings | Type Constructors | `tm_nf` at `Ty l`, 657–678 |
| `sup_f` congruence (children compared at `Vec`) | Congruence | `Type::Wf` arm, 805–823 |
| `elim_Wf` neutral congruence | Congruence for Neutrals | `tm_ne`, 1096–1139 |

Row 2 is the new *kind* discussed in §10.2 — a neutral-type congruence with
a type premise. Row 4 is the row that does the real work: because the
children are compared **at the `Vec` type**, the comparison descends through
§3's negative `Σ` clause and §4's `Unit` irrelevance, and no `Wf`-specific η
is needed or present.

**What the declarative side owes**, added to §7's two rules:

3. The four `Vec`/`Fin` computation rules and `elim_Wf`'s β. Ordinary
   reductions; no new rule *shape*.
4. Whatever `Unit`/`Empty`-formation the §10.3 repair settles on — a
   *change* to a rule already stated in part I, not an addition, and the one
   open item this pass leaves behind.

No new η rule. That is the design's central claim — "store children where
the kernel's η already reaches" — surviving the semantic pass.

---

## 17. Verdict

| former | LR case shape | new definitional risk | layering restriction | verdict |
|---|---|---|---|---|
| `Vec` | **none** — reduces, or is neutral | none | none | invisible; owes one neutral-type congruence, and exposed the open `Unit`-level defect (§10.3) |
| `Fin` | **none** — same | none | none | invisible; owes one neutral-type congruence |
| `Wf` | positive, **finitary** Kripke induction over a Σ-spine | one new lemma (§13), no new shape | contravariant in `N` only — one premise fewer than `W` | goes through |

**The abort criterion is not triggered.** The `Wf` case is a restriction of
`W`'s in three separate senses, each checkable against §5:

- its type rule is `W`'s with a term relation at `Nat` in place of a type
  relation (§11);
- its term relation is `NfEqW` with the subtree quantifier replaced by a
  finite Σ-spine, and is `Wf`-shaped where `NfEqW` is `W`-shaped (§12);
- its layering-restriction case has one contravariant premise where `W` has
  two (§15).

The one thing `W` does not pay for is §13, and that lemma is four cases of
reductions the kernel already performs. Route A (`W` + funext) stays
unchosen; `crates/elab/tests/branching_route_a.rs` stays unchanged as the
costed record of what was not taken.

**Caveats, recorded honestly.** This is a pen-and-paper pass, like part I.
The cases asserted "mechanical" — transitivity and left/right irrelevance
(§15), and the property lemmas for `Wf` other than escape and
reflexivity-of-neutral — were checked for *shape* against `W`'s and not
written out in full. The one place that most deserves a second look before
any mechanization is the composite spine recursion in transitivity (§15),
because it is the only construction in this round that appears twice and was
written out once.

---

# Part III — the `sEq`/`transp` round (sketch, pre-code)

Written 2026-07-28 as step 2 of `docs/sprop-design.md` §8 — *before* any
kernel code, per the sequencing note of `issues/sprop-strict-prop.md`
(postulates cannot de-risk a conversion feature; this sketch is the
de-risk). Unlike parts I–II this is a pass over a design, not a landing:
its job is to state the new obligations precisely, work the cases far
enough to find the shape-level surprises, and check the abort criterion.
Two genuine findings came out of working it; they are §19 and they
*changed the design doc* (§5.2's guard premise) rather than the other way
around.

## 18. `sEq` and `sEmpty` — Id's type rule, Unit's term relation

**Declarative additions (ch. 04-style)** these formers owe: formation and
congruence rules (routine, `Id`/`Unit` shaped); `srefl`/`transp`
congruences and `transp`-β; and two *irrelevance laws* —
`Γ ⊢ p ≈ q : sEq^l(I; a; b)` and the same at `sEmpty^l`, premise-free like
η-`Unit`. The strip rule is also declarative:

```
Γ ⊢ a ≈ b : I @ l
--------------------------------------------------
Γ ⊢ transp^{l,l'}(I; x.P; a; b; e; t) ≈ t : P[b/x]
```

**LR cases.** `sEq`'s type rule is `Id`'s verbatim (§6): whnf both sides,
generic equivalence, `E :: ∀ψ. I ~ I'`, endpoints related at `E(ψ)`.
`sEmpty`'s is a premise-free base case like `Unit`'s. Both **term relations
are total** — `t ~ t'` iff both well-typed at the type, no whnf condition,
no `NfEq` inductive. This is `Unit`'s §4 case wholesale, including both of
its recorded consequences: escape is *not* derivable from term structure
and must come from the irrelevance laws above (which is why they are laws),
and presupposition holds by assumption on the caller. Every property lemma
at these types is vacuous; layering restriction is immediate (no
contravariant premises anywhere — `sEq`'s components are covariant like
`Id`'s, `sEmpty` has none).

## 19. `transp` — two findings from working the term relation

**Finding 1: the naive neutral treatment is *wrong*, not just weak.** A
stuck `transp(I; x.P; a; b; e; t)` does not reduce on its payload — it is
stuck on the proof — so `transp(e; 5)` is a whnf at `Nat`. But the strip
law demands `transp(e; 5) ≈ 5` whenever `a ≈ b`, and `NfEqNat` relates
neutrals only to neutrals: a term relation that classifies strippable
transps as ordinary neutrals cannot validate the strip law at any positive
type. Adding a strip clause to each `NfEq` separately would work but
duplicates the same clause everywhere. The uniform statement: **the LR's
evaluation notion changes from whnf to whnf-then-strip** — evaluate to
whnf; if the head is a `transp` whose endpoints satisfy the strip premise,
replace it by its payload and continue; term relations are read over
*these* normal forms. This is a global-but-uniform edit — it touches the
evaluation notion once, not each former's clauses — and it is the exact
semantic counterpart of the algorithm's whnf-adjacent strip loop
(`docs/sprop-design.md` §5.2). The algorithm and the LR agree that strip
belongs to *evaluation*, not to per-type equivalence: the pleasing
coherence, and the piece with no precedent in parts I–II (every prior
extension added cases; this edits a notion the cases share).

**Finding 2: the strip premise must be declarative convertibility, not
semantic relatedness.** The tempting premise "`a ~ b` at the relation for
`I`" is circular-by-levels: the motive lives at `l'`, the index type at
`l`, and nothing orders them — a term relation at level `l'` would appeal
to a type relation at an arbitrary `l`. Neutrals already solve this
problem: their congruence premises use the *generic equivalence*, not the
LR. The strip premise does the same — `Γ ⊢ a ≈ b : I @ l`, a syntactic
judgment, no level appeal, no circularity — and this is also exactly what
makes the declarative strip rule above well-stated. (Design-doc
consequence, folded back into §5.2: the algorithm's guard query *is* the
algorithmic mirror of a declarative premise, so ch. 08-style completeness
has the usual shape — no new proof obligation kind.)

**The `transp` cases, given the two findings:**

- *β / `srefl`:* weak-head expansion, `J`'s refl-case shape (§6):
  `srefl`'s typing forces `a ≈ b`, the FT turns that into the semantic
  equality that carries `P[a]`'s relation to `P[b]`'s, and the payload
  premise lands.
- *Strippable:* by strip expansion — the evaluation notion of finding 1
  makes this literally the weak-head-expansion property lemma re-proved
  for the extended evaluation; termination of iterated strip is the
  payload being a strict subterm (same argument as the algorithm's).
- *Stuck (guard fails):* an endpoint-keyed neutral clause — `I`, `P`,
  `a`, `b`, `t` premised via generic equivalence as usual, proofs
  **unconditionally related** (their type is `sEq`; §18's total relation).
  Reflexivity-of-neutral and the congruence-for-neutrals law follow the
  `J` pattern with the proof premise deleted.

`elim_sEmpty`: neutral-only eliminator, no β — its arm is the `Empty`
eliminator's with the scrutinee premise weakened to well-typedness
(irrelevance). Nothing else changes.

## 20. The code-layer observers — re-running §6's argument

§6 closed with a warning naming this round: an "irrelevant/definitional-Id
rule" would make the □-observability argument need redoing. Re-run, for
`sEq` at each code type:

- **`sEq^0(□(Δ ⊢ T); box t; box t')`.** The §6 invariant survives because
  it never rested on `Id`'s proofs being relevant: `srefl` *synthesizes*
  `sEq(S; u; u)`, so checking it against endpoints `box t`, `box t'` goes
  through conversion at `□`, which is `==`. Irrelevance collapses the
  *proofs*, not the endpoints — `sEq` at `□` is inhabited by `srefl` iff
  the code is syntactically equal, the same equality the recursor
  dispatches on. `transp` along a neutral such proof is stuck unless the
  boxes are `==` (the guard runs the same syntactic comparison), so no
  coarser equality leaks into any motive. No unbox congruence exists; the
  recursor arms of the FT still case-analyse box *syntax* and never
  consult an `sEq` relation.
- **`sEq^{1+l}(Ty l; A; B)` — the earmark from the issue.** Observes
  *definitional* equality of encodings, irrelevantly. `Id` at `Ty l`
  already observes exactly that propositionally, and term conversion at
  `Ty l` is unchanged by this round, so the observer is new only in that
  its witnesses are collapsed. `transp` with motive `x. El x` moves along
  it, stuck unless `A ≈ B` — which is precisely `El A ≈ El B` territory
  the checker already owns. Verdict: inert, as predicted, and now argued
  rather than flagged.

The §6 strengthening gets a sharper restatement for DESIGN.md: *endpoint
checking goes through conversion, and conversion at `□` is `==`* — a
property `sEq` inherits from the same two facts `Id` did, so both
observers stand or fall together.

## 21. Cross-check: the new laws vs. the algorithm

- Irrelevance laws ⇔ the two `Ok(())` arms (type-directed, ahead of any
  fallback — `Unit`'s §4 ordering note applies verbatim).
- Strip rule ⇔ the whnf-adjacent strip loop; the declarative premise
  `a ≈ b` ⇔ the guarded query, with `NotConvertible` caught (= "premise
  absent, take the neutral clause") and `OutOfFuel` propagated. The
  completeness direction rests on the guard being the algorithmic mirror
  of a declarative premise (§19 finding 2), the usual ch. 08 shape.
- β ⇔ `reduce.rs`; congruence + congruence-for-neutrals ⇔ the `tm_ne`
  arm with proofs skipped. The skip is *justified* by the total relation,
  not a special case of it — one uniform principle, as designed.

## 22. Verdict — against the abort criterion, pre-code

| former | LR case shape | new definitional risk | layering restriction | verdict |
|---|---|---|---|---|
| `sEq` | `Id`'s type rule + total term relation | irrelevance laws (Unit-precedented) | covariant only | goes through |
| `sEmpty` | base case + total term relation | none | trivial | goes through |
| `transp` | endpoint-keyed neutral + **evaluation-notion edit** (§19) | the strip law | no contravariant premises | goes through, one global edit |

**The abort criterion (`sprop-design.md` §7) is not triggered**: no
relevance marks appear in contexts, congruences, or anywhere else — the
strip premise is a declarative-equivalence side condition, and proof
skipping is ordinary typed comparison at a type whose relation is total.

**The standing risk, recorded honestly**: finding 1's edit is *global* —
every term-relation case is re-read over whnf-then-strip normal forms, and
this sketch re-read them for shape, not in full. Parts I–II only ever
added cases; this is the first round that edits a shared notion, and the
full FT pass (step 3 of the design doc's sequencing, with code) is where a
case that secretly depended on "whnf = stuck-or-canonical" would surface.
That pass, not this sketch, retires the risk. If it surfaces relevance
marks after all, the abort criterion fires and the fallback is the
judgmental sort, at the cost `sprop-design.md` §1 itemizes.

# Part IV — the definitions round (rules, and the ch. 07 bill)

Written 2026-07-31 alongside the code
(issues/simulate-conversion-cost.md). This part is different in kind from
I–III: the extension is not a type former but a **binding** form, so the
rules below are ch. 04-shaped rather than LR-shaped, and the ch. 07 work
is *owed*, not done. It is recorded here because the obligations are
ch. 07's and because [[delam-extensions-writeup]]'s standalone document
does not exist yet — when it does, §23–25 are its section on definitions.

## 23. The binding form and its typing

DeLaM ch. 04's global bindings are declarations only:

```text
B ::= g : Ctx | U : Typ_i(Δ, l) | u : Trm_i(Δ ⊢ T @ l)          i ∈ {c,p} / {v,c}
```

We add a body to the third:

```text
B ::= … | u : Trm_i(Δ ⊢ T @ l) := t
```

with the well-formedness rule (extending `⊢_L Ψ`):

```text
   ⊢_L Ψ        Ψ ⊢_L l : Level      Ψ ⊢_p Δ      Ψ; Δ ⊢_p T @ l
   Ψ; Δ ⊢_i t : T @ l        i = c
  ────────────────────────────────────────────────────────────────  (wf-def)
   ⊢_L Ψ, u : Trm_i(Δ ⊢ T @ l) := t
```

Three deliberate constraints:

1. **`i = c`.** Layer v admits only variables (ch. 04's "Note on Layer v
   Rules"), so a definition there would be a renaming; and the binding
   invariant already forbids p and m.
2. **The body is checked at the binding's own layer `i`**, not at p. This
   is what makes δ *layer-preserving*: unfolding `u` at any `j ≥ i`
   produces a term already legal at `j`. Checking it at p instead would
   let `box(u^δ)` be code whose unfolding is not, and preservation at p
   would fail.
3. **The body is scoped in `Δ` over Ψ's prefix**, exactly like `T` — so
   an occurrence at `Ψ, Ψ'` unfolds to `t⇑^{|Ψ'|+1}[δ]`.

The *use* rules are unchanged. `Ψ; Γ ⊢_j u^δ : T[δ] @ l` for `i ≤ j` is
ch. 04 verbatim: a definition is a declaration that additionally knows its
body, which is the whole reason this is one binding form and not two.

## 24. δ, and why it is indexed by the layer

The new computation rule, at the computing layers only:

```text
   u : Trm_c(Δ ⊢ T @ l) := t  ∈ Ψ        j comp
  ─────────────────────────────────────────────────  (δ)
   Ψ; Γ ⊢_j u^δ ⇝ t[δ] : T[δ] @ l
```

and, correspondingly, `u^δ` is **not** neutral at a computing layer when
`u` is defined, while it stays neutral at c.

The layer index is forced, not chosen. Ch. 06 blocks both code-recursion
principles on global variables and compares `box(U^δ)` / `box(u^δ)`
*syntactically*. If δ fired at c, then `box(u^δ) ≈ box(t)` while
`elim^Trm` still dispatched them to different branches — the recursor
would observe a distinction conversion had erased, which is exactly the
coherence property §6 of Part I turns on. So:

- at p/m, `u` denotes its body (definitions are prog's business, since
  running is);
- at c, `u` denotes itself (code is syntax).

This is the run/inspect split the layers already encode, and it is
independently wanted: `.code` carrying stable `u`-references rather than
inlined bodies is what intensional instance keying needs
([[compile-typeclass-design]]).

Two consequences worth stating as invariants:

- **Type-level bindings stay opaque at every layer.** `U : Typ_i(Δ, l)`
  gains no body in this round, so a type reaches δ only through `El ν`.
- **δ never enters a `box`.** Reduction does not descend into `box`, and
  boxed code compares with syntactic equality, so the layer-c guarantee is
  structural rather than a check that could be forgotten. The tests pin it
  from the outside anyway (`crates/kernel/tests/definitions.rs`).

## 25. Conversion: the δ-lazy order

Algorithmically (`conv.rs`), weak-head reduction runs first *without* δ;
if both sides then sit at the same defined head, their spines are compared
first, and only a failure unfolds. Declaratively this is not a new rule —
δ is a reduction, and the spine comparison is the ordinary neutral
congruence — so ch. 08's soundness/completeness story is unaffected in
shape: the heuristic changes *which* derivation the algorithm finds, not
which pairs are related. The guard is `Conv::strip`'s (catch
`NotConvertible`, propagate `OutOfFuel`, no refund), for the same reason:
the verdict must not depend on where the budget died.

## 26. What ch. 07 is owed

Not done in this round; recorded so it is not lost.

1. **Definitional glueing at p.** The logical relation must interpret a
   bodied `u` at a computing layer *by its body*: `⟦u^δ⟧ = ⟦t[δ]⟧`, the
   standard glued interpretation. Every place the LR reasons about a
   global-headed neutral gains a case split on whether the global is
   defined.
2. **Neutral at c.** At layer c the interpretation is unchanged — `u` is
   a neutral, and the Static Code lemma (ch. 05 `lem:dt:static`) still
   applies to boxed occurrences. The obligation is to show the two
   interpretations *cohere* across `box`: the c-interpretation is what
   `□` types see, and nothing at p can reach through.
3. **Fundamental theorem, `u`-cases.** Both recursion principles' `u`
   branches and the variable/global cases redo under the split. Ch. 07's
   generic equivalence is instantiated twice (ch. 04's declarative and
   ch. 06's algorithmic); δ must be added to the first for the second to
   be complete against it.
4. **Termination.** Ψ is a telescope, so δ is well-founded on the global
   index and cannot loop — the argument is one line, but it is the line
   that keeps normalization's induction measure intact.

Nothing here is a new *shape* of obligation: (1) is the textbook glueing
case, (2) is Part I §6's argument re-run one level down, and (4) is
structural. The risk is bulk, not novelty.
