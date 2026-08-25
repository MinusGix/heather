# Ch. 07 pen-and-paper pass for the kernel-v1 extensions

Status: **part I** (§§1–9), the kernel-v1 formers, 2026-07-24. **Part II**
(§§10–17), the `Wf` round, 2026-07-25. **Part III** (§§18–22), the
`sEq`/`transp` round — sketched pre-code 2026-07-28, and **superseded
2026-08-03** by the with-code fundamental-theorem pass that now occupies
those sections. **Part IV** (§§23–26), the definitions round's rules and its
*owed* ch. 07 bill, 2026-07-31. Pen and paper, not mechanized.
Tracking issues: `issues/metatheory-ch07-pass.md` (earmarked from
`issues/kernel-v1-extensions.md`); `issues/wf-former.md` phase 4 for part II;
`issues/metatheory-ch07-sprop.md` for part III;
`issues/metatheory-ch07-definitions.md` for part IV.

The kernel extends DeLaM ch. 04 with six type formers that the paper's
logical relations (ch. 07/07a/07b) never saw: `Id`, `Σ`, `Unit`, `Empty`,
`+`, `W`. Each landed with its LR obligation earmarked but never checked.
This note walks the obligations and records, per former, whether the
fundamental theorem still goes through.

**Conclusion up front: nothing breaks.** No kernel rule needs changing. The
new work is bookkeeping in four known places, plus one genuinely new
definitional shape (`W`'s infinitary constructor case) and two rules that
the *declarative* side owes us (§7).

**What is deliberately absent from this document (2026-07-31).** The NbE
conversion round (`docs/nbe-conversion-design.md`; landed in full the same
day) replaced conversion's
reduction engine with an environment machine over a value domain, and it
creates **no ch. 07 obligation at all** — no former, no binding form, no
judgment, no rule changes, so the logical relations interpret exactly the
system they interpret today. Its one new obligation is *machine adequacy*
(`eval` ≡ ch. 06's `⇝*`, both directions), a ch. 06-level property about an
algorithm; it is stated in that document's §11.2 and registered as a row in
`docs/ch05-06-lemma-audit.md`. The absence is written down here so a reader
of this document does not have to derive it. Part IV's outstanding
definitions bill (§26) is neither discharged nor enlarged by that round:
glued *evaluation* is an implementation of the δ rule, not a new semantics
for it.

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

# Part III — the `sEq`/`transp` round (the with-code fundamental-theorem pass)

Status: **the pass, 2026-08-03**, discharging `issues/metatheory-ch07-sprop.md`
and `docs/sprop-design.md` §7's standing risk. It supersedes the *sketch,
pre-code* of 2026-07-28, which was step 2 of the design doc's sequencing and
whose job was to state the obligations, find the shape-level surprises and
check the abort criterion before a kernel line was written. The sketch did
that and its two findings changed the design doc rather than the other way
around; what it explicitly did **not** do is walk every term-relation case
under the notion it edited. This part does, against landed code.

**Provenance, so the sketch's claims stay traceable.** The house rule is to
annotate corrections in place and date them, not to rewrite a claim that was
once believed. The sketch's five sections map as follows, and each place
where this pass *changed* a sketch claim is marked `Correction (2026-08-03)`
at the point of the change:

| sketch (2026-07-28) | here |
|---|---|
| §18 the two formers | §18, extended with the declarative rule set as landed |
| §19 finding 1 (evaluation-notion edit) | §19 — **corrected**: the edit is not head-only |
| §19 finding 2 (declarative premise) | §19.2, and it now pays twice |
| §19 the three `transp` cases | §21.1–§21.3 |
| §20 the code-layer observers | §20.5 |
| §20's `sEq(Ty l)` bullet | §20.6, its own section, as the bill asked |
| §21 cross-check vs the algorithm | §21.7 |
| §22 verdict, pre-code | §22.5, post-code |

**Conclusion up front.** The abort criterion is **not** triggered, now for a
stated reason rather than an absence of counterexamples (§22.5): the strip
premise reads the context only through ordinary declarative convertibility,
and no `sEq` hypothesis can strengthen that judgment, because the system has
no equality-reflection rule. No relevance mark appears on a context entry,
in a congruence rule, or anywhere else. The logical relations go through
with **no new clause and no clause removed** — the entire semantic cost is
one edited reduction relation, one restated substitution lemma, and one
lemma that was free before (§19.3, §19.4).

The pass is not free of findings, and one of them is a defect. The
evaluation-notion edit reaches the *type* relations as well as the term
relations — automatically, because ch. 06's type reduction has congruence
rules into terms — and the kernel's reduction does not implement that. The
consequence is a second, previously unrecorded instance of the head-only
strip gap, at `Vec`/`Fin` lengths and `El` codes, which
`docs/sprop-design.md` §5.4 currently asserts is fine (§22.4). It is an
incompleteness, never an unsoundness, and it is confined to redundant casts
by the same argument as the term-level instance — but §5.4 owes a
correction, and it is the one thing in this round that a reader of the
design doc would today get wrong.

---

## 18. `sEq` and `sEmpty` — Id's type rule, Unit's term relation

**Declarative additions (ch. 04-style)** these formers owe, as landed:
formation and congruence rules for `sEq^l(I;a;b)` and `sEmpty^l` (routine,
`Id`- and `Unit`-shaped); `srefl` and `transp` congruences; `transp`-β on
`srefl`; the `elim_sEmpty` congruence; and two *irrelevance laws*,

```
Γ ⊢ p : sEq^l(I; a; b)    Γ ⊢ q : sEq^l(I; a; b)
------------------------------------------------
Γ ⊢ p ≈ q : sEq^l(I; a; b)
```

and the same at `sEmpty^l`, premise-free in the way η-`Unit` is (part I §7,
rule 2). The strip rule is declarative too, and its premise is a
convertibility judgment:

```
Γ ⊢ a ≈ b : I @ l
--------------------------------------------------
Γ ⊢ transp^{l,l'}(I; x.P; a; b; e; t) ≈ t : P[b/x]
```

well-typed because `a ≈ b` gives `P[a/x] ≈ P[b/x]`. Being a rule of the
declarative equivalence, it is **closed under the congruence rules of every
former**, exactly as β is: from `transp(…;e;ze) ≈ ze : Nat @ 0` the
`elim_Nat` congruence gives `elim_Nat(…; transp(…;e;ze)) ≈ elim_Nat(…; ze)`,
and the `Vec` congruence gives `Vec^l(T; transp(…;e;ze)) ≈ Vec^l(T; ze)`.
That closure is not optional and cannot be restricted away — there is no
declarative equivalence without congruence — and it is the whole subject of
§19 and §22.

**LR cases.** `sEq`'s type rule is `Id`'s verbatim (§6): reduce both sides,
generic equivalence of the weak head forms, `E :: ∀ψ. I ~ I'`, endpoints
related at `E(ψ)`. `sEmpty`'s is a premise-free base case like `Unit^l`'s,
carrying its level (§10.3's indexing applies to it from birth). Both **term
relations are total** — `t ~ t' @ D` iff both are well-typed at the type, no
weak-head condition, no `NfEq` inductive. This is §4's `Unit` case
wholesale, including both of its recorded consequences: escape is *not*
derivable from term structure and must come from the irrelevance laws above
(which is why they are laws and not derived congruences), and presupposition
holds by assumption on the caller rather than by the structure of the
relation. Every property lemma at these two types is vacuous; the layering
restriction is immediate, since `sEq`'s components are covariant like `Id`'s
and `sEmpty` has none.

One consequence of the total relation is worth stating because it is easy to
misread as a loss. The LR proves nothing about inhabitation at `sEq`, so
consistency does not come from it — that is `Empty`/`sEmpty`'s job (§2).
What *is* true, and is what the round needs, comes from canonicity instead:
a closed term at `sEq^l(I;a;b)` weak-head reduces to a canonical form or a
neutral, there are no closed neutrals, and `srefl` is the only canonical
form at `sEq` (design doc §3), so a closed inhabitant forces `a ≈ b`.
**`sEq` therefore imports no equation it was not already given.** §20.6
depends on this.

---

## 19. The evaluation-notion edit, in full

### 19.1 The notion, stated once

> **Definition (strip-aware weak-head reduction, `⇝ₛ`).** Extend ch. 06's
> reduction — both the type relation and the term relation — with one rule,
>
> ```
> Γ ⊢ a ≈ b : I @ l
> ─────────────────────────────────────────────────  (strip)
> transp^{l,l'}(I; x.P; a; b; e; t)   ⇝ₛ   t
> ```
>
> and *restrict* the congruence rule that reduces a `transp`'s proof to the
> complementary side condition `Γ ⊬ a ≈ b : I @ l`. Everything else is
> ch. 06 verbatim: the same evaluation contexts, the same β rules, the same
> `El`/`Vec`/`Fin` rules for types. Write `⇝ₛ*` for the reflexive-transitive
> closure and read **every** `⇝*` premise of ch. 07/07a — the term premises
> `t ⇝* w` *and* the type premises `T ⇝* W`, i.e. both auxiliary judgments
> `ttypreds` and `ttrmreds` of ch. 06 — over `⇝ₛ*`.

No clause of any logical relation is added, removed or reworded. That is the
sense in which this is an edit to a *shared notion* rather than an extension:
parts I and II each added cases to a fixed notion of evaluation; this round
changes the notion and leaves the cases alone.

Two things follow immediately and are worth having in front of the reader
before the walk.

- **The edit reaches the type relations for free.** Ch. 06's type reduction
  is not independent of terms: `El^l t ⇝ El^l t'` when `t ⇝ t'`, and (our
  extension) `Vec^l(T;k)`/`Fin(k)` reduce by reducing `k`. Since those
  congruence rules quote the *term* reduction, replacing it by `⇝ₛ` makes
  `El^l(transp(…;e;TmNat)) ⇝ₛ* Nat` and
  `Vec^l(T; transp(…;e;ze)) ⇝ₛ* Unit^l` whenever the strip premise holds.
  Nothing has to be said about types separately. This is the point where the
  sketch's phrasing was too narrow, and it is where the kernel and the
  specification part company (§22.4).
- **The strip subsumes `transp`-β.** If the proof reduces to `srefl^l(I;a₀)`
  then well-typedness at `sEq^l(I;a;b)` forces `a ≈ a₀ ≈ b`, so the strip
  premise already holds and the strip fires first. On well-typed terms the
  restricted congruence rule therefore loses nothing (when `a ≉ b` the proof
  provably never reaches `srefl`), and ch. 06's `transp`-β rule is derivable
  in `⇝ₛ`. It is kept in `reduce.rs` anyway, and must be: the *algorithm*
  has to fire β without running a conversion query, which is the whole
  content of design doc §5.1's separation.

> **Correction (2026-08-03) to §19 finding 1 of the sketch.** The sketch
> stated the edit as *whnf-then-strip*: "evaluate to whnf; if the head is a
> `transp` whose endpoints satisfy the strip premise, replace it by its
> payload and continue". Read literally that is a **head-only** notion, and
> it is not strong enough for the logical relations, because the declarative
> strip rule is closed under congruence (§18) and a head-only evaluation
> cannot validate `elim_Nat(…; transp(…;e;ze)) ≈ elim_Nat(…; ze)`. The
> notion the LR needs is the one above: the strip is a *reduction rule*,
> firing wherever ch. 06's evaluation contexts already look for a redex —
> eliminator scrutinees, function positions, `Vec`/`Fin` lengths, `El`
> codes. The sketch's head-only reading is not wrong about anything; it is a
> correct description of **the algorithm**, which is exactly why the
> mismatch was invisible until the two were written down side by side. §22
> is that mismatch, stated as a scoped completeness theorem.

### 19.2 The premise is declarative convertibility, and it pays twice

The sketch's second finding stands unchanged and is load-bearing in two
places instead of one.

The tempting premise — "`a ~ b` at the logical relation for `I`" — is
circular by levels: the motive lives at `l'`, the index type at `l`, and
nothing orders them, so a term relation at `l'` would appeal to a type
relation at an arbitrary `l`, against the transfinite recursion on universe
levels that the whole construction is organized by. Neutrals already solve
this problem, and the strip copies their solution: their congruence premises
appeal to the *generic equivalence*, not to the LR. The strip premise
`Γ ⊢ a ≈ b : I @ l` is a syntactic judgment, makes no level appeal, and is
what makes the declarative rule of §18 well-stated in the first place.

The second payment, which the sketch did not need and this pass does: the
premise has to be **stable under the operations the LR performs on
contexts** — weakening (the Kripke quantifier `∀ψ`), local, global and
universe substitution (the semantic judgments), and lifting between layers
p and m (the layering restriction). A declarative convertibility premise
inherits every one of those from ch. 05's structural lemmas, unchanged. A
semantic premise would have owed each of them separately.

And the *converse* stability, which is the one that decides the abort
criterion:

> **Proposition (weakening does not create strip premises).** If
> `Γ, x : sEq^l(I;a;b) @ l ⊢ c ≈ d : J @ l''` is derivable and `c`, `d`, `J`
> do not mention `x`, then `Γ ⊢ c ≈ d : J @ l''` is derivable.

The reason is that **there is no equality-reflection rule**. `sEq` is
eliminated by `transp`, which moves a term along the equation into a motive;
it never concludes a convertibility judgment from a hypothesis. So a context
entry at `sEq` type is inert for the equivalence judgment, and the strip
premise at `Γ` and at any weakening of `Γ` are the same question. Two
consequences, both wanted:

- neutrals that are strip-normal stay strip-normal under `∀ψ`, which is what
  the Weakening lemma of ch. 07 needs at every neutral clause (§20.4);
- **no context entry has to carry a relevance mark**, because nothing about
  the entry's *type* is ever consulted when deciding whether the strip
  fires. That is the abort criterion, discharged (§22.5).

Substitution is the asymmetric case and stays asymmetric: a substitution
*can* make endpoints convertible that were not, which is why §19.4's
substitution lemma is weaker than ch. 06's, and why §22.3's confinement
argument has an honest limit.

### 19.3 Determinacy survives, and why the formulation was chosen for that

Ch. 06 proves Determinacy twice, once for a single step and once for
multi-step reduction to a normal form, and ch. 07 *consumes* it: the Right
Irrelevance lemma opens with "By determinacy, we know that `T ⇝* Π…` must be
unique" (07:761), and 07a:1092 is the second and last appeal
(`issues/metatheory-lemma-sweep.md`, 2026-07-25, swept for exactly this).
Both appeals are to the **multi-step** form.

`⇝ₛ` keeps both forms:

> **Lemma (determinacy of `⇝ₛ`).** Ch. 06's Determinacy holds verbatim for
> `⇝ₛ`, single-step and multi-step.
>
> *Proof.* Ch. 06's proof is a case analysis showing that at most one rule
> applies at each position. The only new overlap is at a `transp`, where the
> strip rule and the proof-reducing congruence rule could both fire — and
> they cannot, because §19.1 gives them complementary side conditions. The
> strip rule's own side condition is a *judgment*, not a choice: it holds or
> it does not. Every other case is ch. 06's, unchanged. ∎

This is why the notion is formulated as "one rule plus one restriction"
rather than as an unrestricted rule. Adding the strip without restricting
the congruence rule gives a genuinely non-deterministic relation — a
strippable `transp` whose proof also reduces has two one-step reducts — and
recovering unique normal forms would then need confluence plus Newman's
lemma, i.e. termination of reduction, which is the thing ch. 07 is *proving*.
The restriction avoids the circle outright, at the cost of nothing (§19.1,
second bullet).

### 19.4 The one lemma that genuinely weakens

Ch. 06's three substitution lemmas say that reduction *commutes* with
substitution: `t ⇝ t'` implies `t[δ] ⇝ t'[δ]`, and likewise for universe and
global substitutions. For `⇝ₛ` that is **false**, and the reason is exactly
the asymmetry of §19.2: a step by the restricted congruence rule carries the
side condition `a ≉ b`, and `δ` can make `a[δ] ≈ b[δ]`. What survives is the
joinable form, and it is all ch. 07 ever uses:

> **Lemma (substitution, restated for `⇝ₛ`).** If `t ⇝ₛ t'` and `δ` is a
> local (resp. universe, global) substitution into `Γ`, then `t[δ]` and
> `t'[δ]` have a common `⇝ₛ`-reduct; consequently `t[δ] ⇝ₛ* w` iff
> `t'[δ] ⇝ₛ* w`.
>
> *Proof.* If the step was any ch. 06 rule other than the restricted
> `transp` congruence, its side conditions survive substitution and
> `t[δ] ⇝ₛ t'[δ]` directly. Otherwise `t = transp(I;x.P;a;b;e;u)` and
> `t' = transp(I;x.P;a;b;e';u)`; if `a[δ] ≉ b[δ]` the step survives as
> before, and if `a[δ] ≈ b[δ]` then both `t[δ]` and `t'[δ]` strip to `u[δ]`
> in one step. ∎

Everything downstream consumes the lemma through 07b's Reduction Expansion,
which pushes a reduction under a substitution and then applies the LR's weak
head expansion property — and weak head expansion is stated on `⇝ₛ*` to a
*common* form, so the joinable version is exactly what it wants. Nothing
else in ch. 07 needs single-step commutation.

Ch. 06's Soundness lemma (reduction is a sub-relation of the equivalence
judgments) gains one bullet: the strip rule is a declarative rule (§18), so
the extension is immediate. Preservation follows as it does there, because
`P[a/x] ≈ P[b/x]` under the premise.

### 19.5 Where the strip does not reach

Three limits, each of which some later section leans on.

- **Layer c has no reduction at all**, so `⇝ₛ` is a computing-layer notion
  exactly as `⇝` is. Conversion is only ever invoked at p/m
  (`debug_assert!` in `conv_type`/`conv_term`, part I §6's audit), and the
  LR's `j = m` cases quantify code through the *static* code lemma.
- **Evaluation does not enter a `box`.** Reduction has no rule descending
  under `box`, so a `transp` occurring inside boxed code is never stripped,
  at any layer. This is what keeps §6's and §20.5's □-observability argument
  intact: two pieces of code that differ by a redundant cast stay
  distinguishable *as code*, which is the intended semantics and the same
  containment funext gets. `crates/kernel/tests/seq_codes.rs` pins it from
  the outside with a stuck `transp` as code in a non-empty Δ.
- **The strip does not look at the proof.** Its premise mentions only `I`,
  `a`, `b`, so `transp` never matches on the proof's structure — GCST's
  K-avoidance shape, preserved semantically: the LR gains no way to
  case-analyse an inhabitant of `sEq`, which is what would import K.

---

## 20. The walk: every term relation under the edited notion

### 20.1 The criterion for "inert"

The edit changes a term relation's content only where it changes which
normal form a term evaluates to, and it changes that only for a term whose
`⇝`-weak-head form is a strippable `transp`. Such a form is, in ch. 06's
grammar, always a **neutral** (a `transp` is stuck exactly when its proof
is). So the edit can only ever move a term *out of* a clause's neutral case
and into some other case of the same relation. Hence:

> A case is **strip-inert** if it never inspects the shape of the weak head
> form — the total relations and the η/negative relations — or if it has no
> canonical case for the term to move into. A case is **load-bearing** if it
> has a canonical/neutral split, because there the edit is what makes the
> case *correct*: without it a strippable `transp` would be classified as an
> ordinary neutral and the clause would refuse to relate it to the canonical
> form the strip rule says it equals.

Note the direction. In the load-bearing cases the edit does not *repair* a
clause; the clauses are unchanged and were always right. It repairs the
notion they are read over. That is the whole reason the edit is uniform.

### 20.2 The table

| relation | term relation | strip verdict | one-line reason |
|---|---|---|---|
| `Nat` | `NfEqNat` (ze / su / ne) | **load-bearing** | `transp(…;e;5)` is a `⇝`-whnf at `Nat` that must relate to `5`; the `ne` clause would refuse it (the sketch's finding 1, in its original example) |
| `Ty l` (universe) | whnf, `≈g`, then the *type* relation at `El l w` | **load-bearing** | a stripped code changes which type `El l w` is; `El^l(transp(…;e;TmNat))` is neutral, `El^l TmNat` is `Nat` |
| `Π` | applied form, `∀ψ ∀ s~s'` | inert | the clause never names `w`'s shape, only `app(w;s)`; the strip commutes with the η-expansion because a `transp` head is not an `app` head |
| neutral type (`El ν`, `U^δ`, `Vec`/`Fin` at a stuck length, `GlobalTy`) | both sides evaluate to generically-equivalent neutrals | **load-bearing** | the neutrals must be *strip-normal*, else the clause would relate a strippable `transp` to a genuine neutral while the strip rule relates it to a payload |
| level conversion (bureaucratic) | inherits | inert | no evaluation premise of its own |
| `Σ` | projections, `fst`/`snd` | inert | §3 chose the negative reading, so no whnf shape is inspected |
| `Unit^l` | total | inert | vacuously — the relation does not look at either side |
| `Empty^l` | neutrals only | inert | there is no canonical case for a stripped term to move into; a stripped payload at `Empty` is again neutral |
| `+` | `NfEqSum` (inl / inr / ne) | **load-bearing** | `transp(…;e; inl a)` must relate to `inl a`, not sit in the `ne` clause |
| `Id` | `NfEqId` (refl / ne) | **load-bearing** | same, with `refl`; and `refl ~ ν` is *not* a case (part I §6, no K), so misclassification would be a refusal, not a coarsening |
| `W` | `NfEqW` (sup / ne), infinitary | **load-bearing** | same, with `sup`; the subtree premise is unaffected, since it is stated at the outer relation which is itself read over `⇝ₛ*` |
| `Wf` | `NfEqWf` (sup_f / ne), finitary Σ-spine | **load-bearing** | same, with `sup_f`; and the spine recursion is on the `NfEqNat` derivation of the arity (§12), which the `Nat` row already fixed |
| `Vec`, `Fin` | **no case** (§10.1) | inherits | they reduce or are neutral; both rows above cover them, and this is where the edit reaches types |
| `sEq^l(I;a;b)` | total | inert | new former, `Unit`'s case wholesale (§18) |
| `sEmpty^l` | total | inert | new former, ditto |
| `□(Δ ⊢ Ty l)`, `□(Δ ⊢ T @ l)` (`j = m`) | `NfEqM` (box / ne) | **load-bearing** *outside* the box, inert *inside* | `transp(…;e; box t)` at a code type must relate to `box t`; and evaluation never enters the box, so the static code lemma is untouched (§19.5) |
| `Π ℓ` / `Π g` / `Π U` (`j = m`) | applied forms | inert | as `Π`: eliminated form, no shape inspected |

Ten inert, nine load-bearing, and not one clause changed. The nine
load-bearing rows are load-bearing for a single reason stated nine times —
each has a canonical/neutral split — which is the evidence the sketch was
right that the edit is "global but uniform", and the evidence this pass owed
that it is uniform *in fact* and not only in shape.

### 20.3 The three cases worth working out

**`Nat`, and why the clause needs no strip case of its own.** Suppose
`Γ ⊢ t ≈ t' : Nat @ 0` with `t = transp^{0,0}(Nat; x.Nat; a; b; e; su ze)`
and `t' = su ze`, under `Γ ⊢ a ≈ b : Nat @ 0` with `e` a hypothesis. Under
`⇝ₛ` the strip fires at the head, `t ⇝ₛ su ze`, and the `NfEqNat` derivation
is the `su` clause with `ze ~ ze` beneath it. Adding a strip clause to
`NfEqNat` instead — the alternative the sketch rejected — would have had to
be added to `NfEqSum`, `NfEqId`, `NfEqW`, `NfEqWf` and `NfEqM` as well, five
copies of one clause, and each copy would have carried its own
weak-head-expansion and transitivity obligations. The edit pays once.

**The neutral-type case, which is the one that could have gone wrong.** Its
term relation is "both sides evaluate to neutrals that are generically
equivalent". If the evaluation were *not* edited, a strippable `transp` at a
neutral type would be admitted into this clause, and the relation would then
claim `transp(…;e;ν) ~ ν'` for a genuinely unrelated `ν'` whenever the
generic equivalence happened to relate the two stuck forms — while the strip
rule independently says `transp(…;e;ν) ≈ ν`. Transitivity would then relate
`ν` and `ν'`, and the relation would be strictly coarser than declarative
convertibility: **unsound**, not merely weak. Under `⇝ₛ` the clause never
sees a strippable `transp`, because `⇝ₛ`-normal forms are strip-normal by
construction. This is the case that most deserved the walk, and it is the
one the sketch's "re-read for shape" would not have caught, since its shape
is unchanged.

**The `j = m` code cases, where the edit and the firewall meet.** A term at
`□(Δ ⊢ T @ l)` can perfectly well be a `transp` whose payload is a `box`:
`transp^{0,0}(□(Δ ⊢ Ty l); x.□(Δ ⊢ Ty l); A; B; e; box T₁)`. Declaratively
it equals `box T₁` when `A ≈ B`, and `NfEqM` relates a `box` only to
*itself*, so without the edit the pair `(transp(…; box T₁), box T₁)` would
be related by no clause at all. Under `⇝ₛ` the left side evaluates to
`box T₁` and the `box` clause applies, with the same
`⟦Δ ⊢ T₁ @ l⟧` premise it always had. The firewall is untouched because the
strip fires *around* the box and never inside it (§19.5): the code `T₁`
itself is compared by the static code lemma, syntactically, and a `T₁`
containing a redundant cast stays distinct from the `T₁` without one. That
asymmetry is deliberate and is the same one funext gets.

### 20.4 The property lemmas, re-read

Each of ch. 07's `j = p` property lemmas, with what the edit costs it.

| lemma | cost |
|---|---|
| Weakening | nothing, *given* §19.2's proposition: a strip-normal neutral stays strip-normal under `ψ`, because no `sEq` hypothesis can create a convertibility. This is the only property lemma where the abort criterion could have bitten, and it is where it does not. |
| Escape | one bullet in ch. 06's Soundness (§19.4): `⇝ₛ ⊆ ≈`, immediate since the strip rule *is* a declarative rule. Escape then composes as before. |
| Reflexivity of neutral | nothing. The neutrals the LR builds — `app ν s`, `fst ν`, `elim(…;ν)` — are strip-normal whenever `ν` is, since a `transp` is never the head of an application, a projection or an eliminator. |
| Weak head expansion | restated over `⇝ₛ*` and otherwise unchanged; its proof is transitivity of reduction, which `⇝ₛ*` has. This restatement is what the sketch called "strip expansion" and it is not a separate lemma. |
| Symmetry | nothing; the relation is still defined with duplicated `≈g` premises. |
| Left / right irrelevance | nothing, *given* §19.3: the appeal to determinacy (07:761) is to the multi-step form and `⇝ₛ` has it. |
| Reflexivity + transitivity | nothing beyond the above. |
| Layering restriction (07a) | nothing. `sEq`/`sEmpty` add no contravariant premise, and the strip premise is a declarative judgment stable under lifting (ch. 05). |

The one lemma that changes statement is ch. 06's, not ch. 07's, and it is
§19.4's.

### 20.5 The code-layer observers — §6's argument, re-run

Part I §6 closed by naming this round: an "irrelevant/definitional-`Id`
rule" would make the □-observability argument need redoing. Re-run, and it
survives, for a reason that was never about `Id`'s proofs being relevant.

- **`sEq^0(□(Δ ⊢ T @ l); box t; box t')`.** `srefl` *synthesizes*
  `sEq(S;u;u)`, so checking it against the endpoints `box t`, `box t'` goes
  through **conversion**, and conversion at a code type is syntactic
  equality modulo level equivalence (`conv.rs` `Type::CodeTy`/`CodeTm`,
  `code_eq`). Irrelevance collapses the *proofs*, not the endpoints.
  Therefore `sEq` at `□` is inhabited by `srefl` iff the code is
  syntactically equal — the same equality the code recursor dispatches on,
  the §6 conclusion verbatim.
- **`transp` along such a proof** is stuck unless the two boxes are equal,
  because the strip guard runs that same comparison; so no coarser equality
  reaches any motive. And by §19.5 the strip never descends into a box, so
  the recursor arms of the FT still case-analyse box *syntax* and never
  consult an `sEq` relation.
- **No unbox congruence exists**, and part I's funext leak audit is
  unaffected: `sEq`/`srefl`/`transp` add no path from a term-level equation
  to a `box`-level one. The strip is the only new way to conclude an
  equation, and its conclusion is at the *payload's* type, never at `□`.

The §6 strengthening, restated once for both observers: *endpoint checking
goes through conversion, and conversion at `□` is syntactic identity modulo
level equivalence.* `sEq` inherits the property from the same two facts `Id`
does, so the two observers stand or fall together. That is the form
`crates/kernel/DESIGN.md` should carry.

### 20.6 The `sEq(Ty l)` earmark

The issue's third bill item, and the one the sketch argued in passing. The
object is `sEq^{1+l}(Ty l; A; B)` — an *irrelevant* equality of type
**codes**, sitting next to `Id^{1+l}(Ty l; A; B)`, which the kernel has had
since part I. The worry it earmarks is that a definitional observer of
encoding equality is a different kind of thing from a propositional one,
and might make code equality reach somewhere it should not.

It does not, and there are four separate reasons, none of which is "by
analogy with `Id`".

1. **Irrelevance is at the proof, and the endpoints are ordinary terms.**
   The kernel's arm is `TyView::SEq { .. } => Ok(())` — it fires on terms
   whose *type* is an `sEq`, and says nothing about `A` and `B`. Those are
   compared by the `SEq` type congruence (`conv.rs:673–686`) and the `TmSEq`
   encoding congruence (`conv.rs:1076–1090`), both of which compare the
   endpoints at `Ty l` by the ordinary encoding comparison, i.e. exactly the
   comparison the round did not touch. Nothing about term conversion at
   `Ty l` changed in this round.
2. **The observation power is `Id`'s, unchanged; only the witnesses are
   collapsed.** `Id` at `Ty l` already observes definitional equality of
   encodings, propositionally: `refl` checks at `Id(Ty l; A; B)` iff
   `A ≈ B`. `srefl` checks at `sEq(Ty l; A; B)` under the same condition and
   by the same route. The difference is downstream: all proofs of the
   `sEq` are definitionally equal, and UIP at it is the irrelevance arm
   firing rather than a theorem.
3. **Its eliminator can never widen type equality.** The interesting motive
   is `x. El x`, giving `transp^{1+l,l}(Ty l; x.El x; A; B; e; t) : El^l B`
   from `t : El^l A`. The strip fires exactly when `A ≈ B` at `Ty l` — which
   is exactly the query that decides `El^l A ≈ El^l B`. So a `transp` at
   this motive is *invisible* precisely when the two types were already
   convertible, and *stuck* otherwise; in neither case does it produce a new
   type equation. This is the precise content of "inert", and it is a
   statement about the guard, not an analogy.
4. **It imports no equation into the empty context.** By §18's canonicity
   remark, a closed inhabitant of `sEq(Ty l; A; B)` forces `A ≈ B`. So the
   former cannot be used to *postulate* a code equality; a hypothesis of
   that type is available only under a binder, where §19.2's proposition
   says it strengthens no convertibility judgment.

**LR side, since the earmark is a ch. 07 one.** `sEq`'s type-relation rule
is `Id`'s (§18), so relating `sEq^{1+l}(Ty l; A; B)` to
`sEq^{1+l}(Ty l; A'; B')` needs `E :: ∀ψ. Ty l ~ Ty l` — the universe rule,
a base case at `1+l` — and the endpoints related at `E(ψ)`, which is the
universe *term* relation: evaluate both at `Ty l`, generic equivalence, then
the type relation at `El l w ~ El l w'`, one universe level down. The
recursion descends, exactly as `Id` at `Ty l` already did, and no new
well-foundedness question arises. The term relation at the `sEq` itself is
total and therefore inspects nothing.

**Verdict: inert, and for reasons 1–4 rather than by analogy.** The one
invariant it rests on is §20.5's, shared with `Id`. If a future round ever
relaxes endpoint checking at code types — a "conversion up to β for code"
convenience is the shape to watch for — both observers move together and
this section, not just §6, has to be redone.

---

## 21. Fundamental theorem: the new arms, and the cross-check

The arms below are the ones the four new rule groups owe. Everything else in
07b is untouched, because §19.1 added no clause: the existing arms are the
existing arms, read over the edited evaluation.

### 21.1 `sEq`/`sEmpty` formation, `srefl`, and `transp`-β

**Formation congruences** are `Id`'s and `Unit`'s. `sEq`: from `I ~ I'`,
`a ~ a'` and `b ~ b'` conclude `sEq^l(I;a;b) ~ sEq^l(I';a';b')`, the premises
feeding `E` and the endpoint conditions directly. `sEmpty^l`: a
premise-free base case, level carried.

**`srefl` congruence** is the shortest arm in the document: the term
relation at `sEq` is total, so the arm has only to produce well-typedness of
both sides at the type, which the semantic typing premises give. Note what
this does *not* need — no relation between the two `srefl`s' annotations,
and no appeal to the endpoints being related beyond what formation already
required.

**`transp`-β.** `transp(I;x.P;a;b;srefl^l(_;_);t) ≈ t : P[b/x]`.
Semantically this is subsumed by §21.2, because `srefl`'s typing forces
`a ≈ b` (§19.1). Written on its own it is `J`'s refl-case shape from part I
§6: reduction expansion carries the redex to `t`, and the FT turns `a ≈ b`
into the semantic equality that transports `P[a/x]`'s relation to
`P[b/x]`'s, where the payload premise lands.

### 21.2 The strip rule's arm

The obligation is: from `Γ ⊢ a ≈ b : I @ l` and semantic well-typedness of
the `transp`, conclude
`⊨ transp^{l,l'}(I;x.P;a;b;e;t) ≈ t : P[b/x] @ l'`.

Under §19.1 the left side `⇝ₛ`-reduces to `t` in one step, so the arm is a
single appeal to **weak head expansion** (§20.4) — the LR is closed under
`⇝ₛ`-expansion on either side, and the right side is already related to
itself by the semantic typing premise. The premise `a ≈ b` travels under the
semantic judgment's substitutions by ch. 05's substitution lemma, which is
the second payment of §19.2.

Iterated strips terminate because the payload is a strict subterm, the same
measure the algorithm's loop uses; and nothing forces the LR to bound the
iteration, since `⇝ₛ*` is a closure, not a procedure.

The arm is the semantic counterpart of the design doc §5.2 loop, and the
correspondence is now exact in a way the sketch could only assert: the
declarative premise is the guarded query, the reduction step is the loop
body, and the strict-subterm measure is the loop's termination argument.

### 21.3 The stuck-`transp` congruence arm

Reached when the strip premise fails on both sides, i.e. two genuinely stuck
transports. The arm is the endpoint-keyed neutral congruence, and it
**inverts `J`'s discipline**: `J` compares its proof structurally because
the proof is its scrutinee and neutrality is keyed on it; `transp`'s
stuckness is keyed on the *endpoints*, so two stuck transports over
different neutral proofs must still be related.

- `I`, `x.P`, `a`, `b`, `t` are premised through the generic equivalence at
  their §4-of-the-design-doc types — motive under `Γ, x : I`, payload at
  `P[a/x]`, left-biased — as any congruence-for-neutrals law does.
- The **proofs are related unconditionally**, because their type is `sEq`
  and §18's term relation there is total. This is not a special case in the
  arm; it is the ordinary typed comparison at a type whose relation happens
  to be total, which is the "one uniform principle" the design promised.
- Reflexivity of neutral then supplies the conclusion at the synthesized
  type `P₁[b₁/x]` at `l'₁`, and it applies because the case hypothesis
  (`a ≉ b`) is exactly the statement that the `transp` is **strip-normal**.
  That is the one place where the arm consults §19.1 rather than ch. 06.

`crates/kernel/src/conv.rs:1609–1650` is this arm, field for field, with the
proofs deliberately not compared.

### 21.4 `elim_sEmpty`

Neutral-only eliminator, no β (nothing canonical to fire on). The arm is
`Empty`'s (part I §2) with the scrutinee premise weakened to
well-typedness: the two scrutinees are related by the total relation at
`sEmpty`, so the arm never inspects them.

One detail the sketch waved through and this pass owes, because the kernel
does it too (`conv.rs:1365–1379`, scrutinee `_`): the arm must conclude at
the *instantiated* motive, and the two sides' instances are `M₁[e₁/x]` and
`M₂[e₂/x]` with `e₁ ≠ e₂`. They agree because `e₁ ≈ e₂` by the irrelevance
law, and the motive congruence then transports one instance to the other.
So the left-biased choice in the algorithm is not a heuristic here — it is
forced to be correct by the same law that lets the scrutinees be skipped.
The same remark covers `transp`'s synthesized `P₁[b₁/x]`, where instead the
endpoints *are* compared and no appeal to irrelevance is needed.

Large elimination (`elim_sEmpty^{l,l'}(M;e) : M` for any `M : Type @ l'`) is
`Empty`'s discipline verbatim; and as with `Empty`, in the empty local
context there are no neutrals at `sEmpty`, so the clause is vacuous there —
the §2 consistency gain, reused.

### 21.5 The irrelevance rules

`Γ ⊢ p ≈ q : sEq^l(I;a;b)` and `Γ ⊢ p ≈ q : sEmpty^l`. Semantically
immediate from §18's total relation. The content is entirely in **escape**:
the LR must hand back a *generic equivalence* between `p` and `q`, and there
is no term structure to derive it from, so the generic equivalence must have
the law. That is why these are laws of the interface and not derived
congruences, and it is §4's `Unit` situation repeated for the second and
third time. The second instantiation discharges them with two `Ok(())` arms
(`conv.rs:1191`, `conv.rs:1196`), type-directed and ahead of any structural
fallback — §4's ordering note applies verbatim, and the kernel gets it right
for the same reason it does at `Unit`.

Π/Σ-closure of irrelevance needs no arm at all: it is the existing η
recursion bottoming out in these two arms (design doc §1), and semantically
it is the `Π`/`Σ` clauses' *applied*/*projected* forms bottoming out in the
total relation. No closure rule exists to have an arm.

### 21.6 The arms the edit disturbs, and the one it does not repair

The edit is to a shared notion, so in principle every arm is affected. In
fact only one family reads the notion at a place where the strip can change
the answer: the arms whose premise is a **term** relation feeding a **type**
weak head form.

- **`Vec`- and `Fin`-formation** (`⊨ Vec^l(T;k) @ l` from `⊨ k : Nat @ 0`).
  Part II §10.1 discharges these by case-splitting on the `NfEqNat`
  derivation of the length and inheriting the reduct's clause through weak
  head expansion. Under `⇝ₛ` the length is stripped first, so at
  `k = transp(…;e;ze)` with convertible endpoints the split lands in the
  `ze` case and the arm concludes through `Unit^l`, as it must. Semantically
  the arm goes through.
- **`El`-congruence** (`⊨ El^l s ≈ El^l s'` from `⊨ s ≈ s' : Ty l`).
  Identical, with the universe term relation in place of `NfEqNat`.
- **Every eliminator congruence** (`elim_Nat`, `case`, `elim_W`, `elim_Wf`,
  `J`, `fst`/`snd`, `app`) reads its scrutinee premise as a term relation
  and inducts on the corresponding `NfEq*` derivation. §20.2's rows have
  already put the stripped form in that derivation, so no arm changes.

The arms go through. **The algorithm does not implement the notion they are
read over**, and that is §22 — stated as a completeness gap rather than a
soundness one, because the LR is the specification and the algorithm is the
under-approximation.

### 21.7 Cross-check: the new laws vs. the algorithm

| new law | kind | `conv.rs` |
|---|---|---|
| `sEq` type congruence (endpoints compared as terms) | Type Constructors | `ty_nf`, 671–686 |
| `sEmpty` type congruence (level only) | Type Constructors | `ty_nf`, 694–699 |
| `TmSEq` / `TmSEmpty` as term encodings | Type Constructors | `tm_nf` at `Ty l`, 1076–1090 and 1100–1106 |
| `srefl` congruence *(subsumed by irrelevance)* | Congruence | `TyView::SEq => Ok(())`, 1191 |
| irrelevance at `sEq` | Congruence | same arm |
| irrelevance at `sEmpty` | Congruence | `TyView::SEmpty => Ok(())`, 1196 |
| strip rule | **evaluation** | `Conv::strip`, 561–586, called from `Conv::tm_w`, 950–955 |
| `transp`-β | reduction | `reduce.rs:390–397` |
| `transp` neutral congruence, proofs skipped | Congruence for Neutrals | `tm_ne`, 1609–1650 |
| `elim_sEmpty` neutral congruence, scrutinees skipped | Congruence for Neutrals | `tm_ne`, 1364–1379 |

Two rows deserve their reading spelled out.

- The **strip row is the only row in this document, across four parts, whose
  "kind" is not a law of the generic equivalence.** It is a rule of the
  evaluation both instantiations quantify over, which is why it appears here
  as a row about `Conv::strip` rather than about an arm. The guard's
  semantics are the algorithmic mirror of the declarative premise: catching
  `NotConvertible` is "the premise is absent, take the neutral clause";
  propagating `OutOfFuel` is "the shared budget is spent and the verdict
  must not depend on where it died".
- The **two skip rows are justified by the total relation, not by a special
  case of it.** Skipping is the irrelevance arm applied, and §21.4 shows the
  skip is not merely harmless but *required* for the left-biased result type
  to be correct.

---

## 22. Completeness, scoped to the head-only strip

### 22.1 The two evaluations, side by side

- **Specification** (§19.1): `⇝ₛ*`, the strip firing wherever ch. 06's
  evaluation contexts look for a redex.
- **Algorithm**: ch. 06's `⇝*` to weak head form (`reduce.rs`, entirely
  strip-blind), followed by `Conv::strip`'s loop applied to the **outermost
  head only** (`conv.rs:950–955`, inside `Conv::tm_w`, after the δ stage).
  Call it `⇓ₕ`.

> **Addendum (2026-08-03, from the sweep's §19 property round).** The
> algorithm differs from `⇝ₛ` *twice*, not once: besides stripping head-only,
> `reduce.rs` applies the `transp`-proof congruence **unconditionally**
> (`reduce.rs:390–407` — `srefl` head ⇒ β, otherwise reduce the proof, no
> endpoint query), i.e. it implements the unrestricted congruence of `⇝`,
> not §19.1's restricted half of `⇝ₛ`. The two differences cancel: §19.1's
> restriction exists solely so the strip and the congruence never overlap
> (§19.3), and `reduce.rs` has no strip rule, so its relation is
> deterministic without it — the proof reductions the restriction forbids
> are exactly the ones the strip would have pre-empted, and here nothing
> pre-empts them. Consequence for testing: determinacy of `⇝ₛ` has no
> step-level kernel counterpart, so
> `seq_transp.rs::strip_and_proof_reduction_have_complementary_side_conditions`
> states it as a property of *conversion* (all proof faces of a strippable
> `transp` identify with the payload; none does at inconvertible endpoints).

`⇓ₕ` computes `⇝ₛ`-normal forms for terms whose strippable transports all
sit at the head, and ordinary `⇝`-normal forms otherwise. It is a strict
under-approximation of `⇝ₛ*`, and the difference is not an accident of
implementation: making the strip a congruence in the algorithm means
stripping wherever reduction looks for a redex, i.e. putting the strip into
`reduce.rs`. That is precisely what the round refused, on the TYPES 2024
argument the design doc §1 quotes — it makes reduction and conversion
mutually recursive, and it destroys the determinism of `⇝` that §19.3 works
to preserve.

Half-measures were considered and do not help. Stripping inside
`tm_nee_c`'s scrutinee positions would rescue only the case where *both*
sides are stuck eliminations; the measured failure is `elim(cast)` (neutral)
against `elim(payload)` (β-fired, hence canonical), where the type-directed
dispatch in `tm_nf` rejects before any spine comparison is reached. **The
gap is structural, not an omission.**

### 22.2 The statement

> **Theorem (soundness, unchanged).** If the algorithm accepts, the two
> terms are declaratively convertible. Every strip it performs is an
> instance of §18's declarative rule, and the guard's failure path returns
> to the ordinary neutral comparison.
>
> **Theorem (completeness, scoped).** The algorithm is complete for the
> declarative equivalence **restricted to derivations that use the strip
> rule only at the head of a compared term** — equivalently, for the pairs
> whose logical-relations witnesses can be read over `⇓ₕ` in place of
> `⇝ₛ*`. That relation strictly contains the strip-free system's
> convertibility (the head-position strips are a genuine gain, and are what
> the 2b acceptance measures) and is strictly contained in the declarative
> equivalence of §18.
>
> It is **not** complete for the declarative equivalence of §18. The
> counterexample is measured and pinned, not hypothetical:
> `crates/elab/tests/indexed_route_2b.rs::index_casts_are_invisible_through_the_strip`
> asserts `cast ≈ payload` and, as a deliberate negative,
> `elim(cast) ≉ elim(payload)`.

The scoping is stated explicitly because the natural thing to reach for is
wrong here. The TYPES 2024 completeness remark — eagerly applying
Cast-Eq-Left/Right loses no solutions, because when strip and congruence
both apply all four types are convertible — is about *not needing to
backtrack over which rule to apply*, and it is what design doc §5.2 cites to
justify the per-side loop needing no backtracking hygiene. It says nothing
about a strip that is never *reached*. Their formulation bundles three rules
that backtrack; ours is a per-side loop that does not, and the price of not
backtracking is that the loop only ever looks where it is standing.

### 22.3 The confinement, argued

The bill asks for the confinement to redundant casts to be argued rather
than asserted. Here is the argument.

> **Definition (redundant-cast erasure).** `⌊t⌋` is obtained by repeatedly
> replacing an innermost occurrence of `transp^{l,l'}(I;x.P;a;b;e;u)` whose
> endpoints satisfy `Γ ⊢ a ≈ b : I @ l` (in the context of the occurrence)
> by `u`, until none remains.
>
> **Proposition.** (i) `⌊·⌋` terminates, because each replacement strictly
> decreases term size. (ii) `Γ ⊢ t ≈ ⌊t⌋ : T @ l`, because each replacement
> is an instance of §18's strip rule under the congruence rules, well-typed
> by `P[a/x] ≈ P[b/x]`. (iii) Erasure neither creates nor destroys
> redundancy elsewhere: endpoints are erased along with everything else, and
> by (ii) `a ≈ b` iff `⌊a⌋ ≈ ⌊b⌋`, so the fixpoint is reached and is
> redundancy-free. (iv) On redundancy-free terms the strip rule is nowhere
> applicable, so the declarative equivalence restricted to them coincides
> with the strip-free system's, for which completeness is the ordinary ch. 08
> theorem with no scoping at all.
>
> **Corollary.** Every pair the algorithm misses contains a *redundant*
> cast — a `transp` at convertible endpoints, i.e. one whose deletion the
> type system itself sanctions — in a non-head position. There is no pair
> requiring a *load-bearing* cast to be stripped, because a load-bearing
> cast is by definition one whose endpoints do not convert, and those are
> never stripped by anyone.

That is the precise sense in which the gap sits "at exactly the terms nobody
needs", and it is why the 2b generator's rule — never emit a cast at
convertible endpoints, i.e. emit only `⌊·⌋`-fixed terms — is the right
discipline rather than a workaround.

> **The honest limit, recorded rather than glossed.** `⌊t⌋ = t` is **not
> preserved by reduction**. The term `(λx. transp(I;x.P;x;b;e;u)) a` is
> redundancy-free — in `Γ, x : I` the endpoints `x` and `b` do not convert —
> and its β-reduct need not be. So a source-level no-redundant-casts
> discipline is *necessary but not sufficient*: it guarantees that nothing
> the generator emits *starts* in the gap, not that nothing reaches it. What
> bounds the residual risk is the direction of failure. The gap can only
> ever produce a spurious `NotConvertible`; it cannot produce an unsound
> accept (soundness is unconditional), and it cannot produce
> non-termination (the guard spends from the same fuel account, and every
> strip pays `spend()`). A generated program that meets it fails visibly and
> at check time.

### 22.4 The finding: the gap reaches the *type* relations, and §5.4 says otherwise

`docs/sprop-design.md` §5.4's first derived fact reads:

> `Vec(D; transp(e, n)) ≡ Vec(D; n)`: neutral `Vec` types compare
> componentwise on lengths *as terms*, where the strip fires. Stuck
> type-level reduction needs no help.

**This holds only when the stripped length is itself stuck, and the
qualifier is missing.** At a *canonical* length it fails, and the failure is
in the kernel, not only on paper:

- `reduce.rs:299–312` reduces `Vec^l(T;k)` by stepping `k` with
  `step_term_delta`, which is strip-blind; `reduce.rs:2143` and `:2172`
  decide `Vec`/`Fin` normality by `is_neutral_term(len)`; and
  `reduce.rs:2194` defines `is_neutral_term(Transp{proof,..})` as
  `is_neutral_term(proof)`. So for a hypothesis `e : sEq^0(Nat; a; ze)`
  with `Γ ⊢ a ≈ ze`, the type `Vec^l(T; transp(Nat; x.Nat; a; ze; e; ze))`
  is a **weak head normal neutral type**, while `Vec^l(T; ze)` reduces to
  `Unit^l`. `ty_nf` then compares a `Vec` view against a `Unit` view and
  returns `NotConvertible`, although the two types are declaratively
  convertible by §18's strip rule under the `Vec` congruence.
- The identical thing happens at `Fin(transp(…;e;ze))` versus `Empty^0`, and
  at `El^l(transp(…;e;TmNat))` versus `Nat` — `reduce.rs:220–288` steps an
  `El`'s code with the same strip-blind term step, and `:2140`
  (`Type::El { tm, .. } => is_neutral_term(tm)`) makes a stuck code a
  neutral type. Three type-former positions, one cause.

Why it was not caught: `crates/kernel/tests/seq_transp.rs::vec_at_a_transported_length_strips`
exercises `Vec(Nat; transp(e; n))` against `Vec(Nat; n)` with `n` a **context
variable**, so both sides stay neutral `Vec` types and the componentwise
length comparison strips at the head, where the algorithm does look. The
canonical-length case — the one where the length's strip unblocks a
*type-level* reduction — is the untested axis. It is precisely
`docs/testing-generated-terms.md`'s "literal *and* neutral scrutinee" axis,
applied to a length rather than a scrutinee, and this is the sixth live
defect that document's axes would have caught.

**What this is and is not.** It is the same head-only gap as the term-level
one, in a position the 2b acceptance did not reach, and §22.3's confinement
covers it unchanged: the offending length is a redundant cast. It is
therefore an incompleteness, not a soundness hole, and it needs no kernel
change to be *sound*. What it does need:

1. **A design-doc correction** at `docs/sprop-design.md` §5.4, first bullet:
   the derived fact holds at a stuck length; at a canonical length the strip
   would have to fire inside a type-level reduction, which the head-only
   strip cannot do. This is the one place a reader of the design doc would
   today believe something false, and it is stated here rather than fixed
   because `crates/` and the design doc's frozen rule set are out of this
   pass's scope.
2. **A note to `issues/indexed-families.md`**, whose route-2b generator is
   the customer: the no-redundant-casts rule now has to be read as covering
   `Vec`/`Wf` *index* positions, not only value-level casts. A forded arity
   `n[a/x]` that reduces to a canonical numeral through a redundant cast
   would meet this. Nothing in the landed prototype does, but the rule as
   currently written does not obviously say so.
3. **Two tests worth adding when someone is next in that file**, both
   negatives pinning current behaviour rather than aspirations:
   `Vec^l(T; transp(…;e;ze))` against `Unit^l`, and
   `El^l(transp(…;e;TmNat))` against `Nat`.

### 22.5 Verdict — against the abort criterion, post-code

| former | LR case shape | new definitional risk | layering restriction | verdict |
|---|---|---|---|---|
| `sEq` | `Id`'s type rule + **total** term relation | irrelevance law (`Unit`-precedented) | covariant only | goes through |
| `sEmpty` | premise-free base + total term relation | irrelevance law | trivial | goes through |
| `transp` | endpoint-keyed neutral congruence + **the evaluation-notion edit** (§19) | the strip rule, and the substitution lemma it weakens (§19.4) | no contravariant premise | goes through |
| `elim_sEmpty` | `Empty`'s arm, scrutinee premise weakened | none | trivial | goes through |

**The abort criterion (`sprop-design.md` §7) is not triggered.** The
criterion asks whether the layered LR can state the strip closure without
threading relevance marks through context entries or the congruence rules.
It can, and the pass can now say *why* rather than only *that*:

- **No congruence rule carries a mark.** The strip is not a congruence rule
  at all; it is a rule of the evaluation both instantiations quantify over
  (§19.1, §21.7). Congruence rules are untouched, which is why no clause of
  any logical relation changed.
- **No context entry carries a mark.** Deciding whether the strip fires
  consults `Γ` only through the ordinary declarative convertibility
  judgment, and §19.2's proposition says an `sEq` hypothesis cannot
  strengthen that judgment, because the system has no equality-reflection
  rule. The context's *relevance structure* is therefore never queried; a
  mark would have nothing to mark.
- **Proof skipping is ordinary typed comparison** at a type whose relation
  is total — one uniform principle, applied at `sEq` and `sEmpty`, and
  applied again by §21.4 to make the left-biased motive instance correct.

**The standing risk of §7 is retired, as stated.** The risk was that the
global edit would turn up a case that secretly depended on
"whnf = stuck-or-canonical". §20 walked all nineteen relations: ten are
strip-inert, nine are load-bearing, none needed a new clause, and the single
case that could have gone *wrong* rather than merely weak — the neutral-type
relation, where admitting a strippable `transp` as a neutral would have made
the relation strictly coarser than convertibility — is closed by the edit
itself, because `⇝ₛ`-normal forms are strip-normal by construction. The
semantic cost of the whole round is one edited reduction relation, one
weakened substitution lemma (§19.4), and one determinacy proof re-run
(§19.3).

**What replaces it is narrower and named**: the algorithm's evaluation is
`⇓ₕ`, not `⇝ₛ*`, so completeness is scoped (§22.2), the scope is confined to
redundant casts (§22.3), and the confinement has an honest limit —
redundancy-freeness is not preserved by reduction, so the generator's
discipline is necessary and not sufficient. The one item that leaves this
document owing something to another is §22.4: `docs/sprop-design.md` §5.4
overstates a derived fact, and the type-level instance of the gap
(`Vec`/`Fin` lengths, `El` codes) is unrecorded and untested.

**Caveats, recorded honestly.** This is a pen-and-paper pass like parts I
and II, against landed code rather than a design. The cases marked inert in
§20.2 were checked against the criterion of §20.1 and not written out one by
one; the criterion is what carries them, and it is a single argument
(a strippable `transp` is always a neutral, so the edit can only move a term
out of a neutral clause), so the exposure is that one argument rather than
ten. The three property lemmas whose cost is recorded as "nothing" in §20.4
— symmetry, reflexivity+transitivity, and the layering restriction — were
checked for the *shape* of the dependency on evaluation and not re-proved.
The place that most deserves a second look before any mechanization is
§19.4's substitution lemma, because it is the only statement in this round
that differs from the one ch. 06 proves, and everything downstream consumes
it through a single intermediary (07b's Reduction Expansion).


# Part IV — the definitions round (rules, and the ch. 07 bill)

Written 2026-07-31 alongside the code
(issues/simulate-conversion-cost.md). This part is different in kind from
I–III: the extension is not a type former but a **binding** form, so the
rules below are ch. 04-shaped rather than LR-shaped, and the ch. 07 work
is *owed*, not done. It is recorded here because the obligations are
ch. 07's and because [[delam-extensions-writeup]]'s standalone document
did not exist yet. That document now does (`docs/delam-extensions.md`,
2026-08-06): its §14 restates §§23–25 in the paper's rule style, and is
the presentation to cite; this part stays as the original record, with
the ch. 07 bill (§26) still owed and still living here.

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

## 27. Squash: normalizing-total irrelevance

`Squash^l A` (`∥A∥`) is the first irrelevant former whose eliminator
computes by inspecting an inhabitant. Its logical-relation clause therefore
cannot reuse `Unit`/`sEq`/`sEmpty`'s unqualified total relation. The term
relation at `∥A∥` is **normalizing-total**:

```text
t ~ t' : ∥A∥  iff  t ⇓ w and t' ⇓ w' for some w,w'.
```

No relation is required between `w` and `w'`, and in particular no relation
is required between the payloads of two `squash` constructors. This exactly
matches the algorithm: conversion first evaluates both terms to WHNF, then
the type-directed squash arm accepts without inspecting either result. It
also prevents irrelevance from hiding divergence or fuel exhaustion, which
would be unsound for the eliminator's operational case split.

The dependent eliminator stores the inner family `B(z)` and constructs its
outer result former itself:

```text
q : ∥A∥
z : ∥A∥ ⊢ B(z) type
x : A ⊢ b(x) : ∥B(squash x)∥
----------------------------------
ind_∥∥(q; z.B; x.b) : ∥B(q)∥
```

For the fundamental theorem, normalize the two scrutinees independently.
A constructor head uses beta and semantic substitution; a neutral head
produces the corresponding neutral elimination. Either way the results are
again related by the normalizing-total clause. Closed canonical forms are
`squash a`: a closed well-typed neutral is impossible by the existing
canonicity argument, while normalization supplies a WHNF. The witness `a`
is retained by syntax (and hence visible to code recursion) but is absent
from the live term relation.

The code-layer case is ordinary structural recursion. `TmSquash`,
`squash`, and `elim_Squash` have distinct branches, so quotation can inspect
the witness and eliminator syntax even though live conversion forgets the
witness. No readback rule crosses the code firewall.
