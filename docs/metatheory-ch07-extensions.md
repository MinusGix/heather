# Ch. 07 pen-and-paper pass for the kernel-v1 extensions

Status: first full pass, 2026-07-24. Pen and paper, not mechanized.
Tracking issue: `issues/metatheory-ch07-pass.md` (earmarked from
`issues/kernel-v1-extensions.md`).

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

`Empty` is the degenerate positive: type rule with no component premises,
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

`Unit` has no eliminator; η is definitional and total (`conv.rs`:
`Type::Unit => Ok(())`).

**LR case.** Type rule: both sides reduce to `Unit`. Term relation: `t ~ t'`
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
exhaustive over well-typed layer-`c` syntax. Counted against `term.rs`:

- **Type formers at layer `c`**: `Nat`, `Π`, `Ty`, `El`, `Id`, `Σ`, `Unit`,
  `Empty`, `+`, `W` = 10, matched by `ty_nat`, `ty_pi`, `ty_ty`, `ty_el`,
  `ty_id`, `ty_sigma`, `ty_unit`, `ty_empty`, `ty_sum`, `ty_w` = 10.
  (`GlobalTy` is the blocked/neutral rule, not a branch.)
- **Term formers at layer `c`**: `Var`, `TmNat`, `TmPi`, `TmTy`, `TmId`,
  `TmSigma`, `TmUnit`, `TmEmpty`, `TmSum`, `TmW`, `Zero`, `Succ`,
  `ElimNat`, `Refl`, `J`, `Pair`, `Fst`, `Snd`, `Triv`, `ElimEmpty`, `Inl`,
  `Inr`, `Case`, `Sup`, `ElimW`, `Lam`, `App` = 27, matched one-for-one by
  the 27 `tm_*` branches. (`GlobalTm` is the blocked rule.)

10 + 27 = 37, the bundle `conv.rs` documents. Exhaustive; the recursor arms
have no gap.

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
