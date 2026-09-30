# UIP is not derivable without `transp`: a groupoid-model argument

Status: **paper argument, 2026-09-30**. §3 and the two counterexamples of
§3.4 and §5 are **mechanized** (`../Lean/delam/probes/NoUipComponents.v`,
closed under the global context). §4 is argued, and was self-reviewed
against the Coq formalization's rules the same day (§4.4). It has not
been independently reviewed.
Owed by `docs/iwf-former-design.md` §12.3 before that rule set freezes.
The rule set in question is the revised one: `docs/sprop-design.md` with
its 2026-09-30 revision (no `transp`, no strip), plus `IWf`/`DVec`.

**Claim.** The statement

```
UIP₀ := Π(p q : Id^1(Ty 0; ⌜Bool⌝; ⌜Bool⌝)). Id(p; q)       (⌜Bool⌝ := TmSum(TmUnit, TmUnit))
```

has no closed inhabitant. So UIP is not a theorem of the rule set,
not even at the smallest universe. By contrast, UIP at `Nat` and at
first-order data *is* a theorem, by Hedberg, and the model agrees (§5).

**Method.** A model in which every rule holds and `UIP₀` is empty. The
model is Hofmann and Streicher's groupoid model (*The groupoid
interpretation of type theory*, 1998), extended to Heather's formers.
Most of the extension is routine. Two pieces are not:
- the strict propositions (§3), for which the lemma is proved below;
- DeLaM's global contexts and `□` (§4), which are argued by
  stratification.

§6 lists exactly what is assumed.

---

## 1. Why the removed `transp` mattered

With a relevant `transp`, UIP is derivable
(`../Lean/delam/probes/UipProbe.v`: `sEq` irrelevance, `transp` into any
motive, and β at `srefl`, even as a propositional equation). Any model of
this document's kind therefore *cannot* validate that `transp`. §3.4 shows
where it fails, as a sanity check on the construction. It also shows that
`transp` *restricted to strict motives* is validated, so re-adding that
restricted form stays UIP-free, as `docs/iwf-former-design.md` §7 claims.

---

## 2. The model, standard part

Following Hofmann and Streicher:
- a **context** is a groupoid;
- a **type** over `Γ` is a split family, i.e. a functor `A : Γ → Gpd`;
- a **term** is a section: an object `a(γ) ∈ A(γ)` for each `γ`, and for
  each `α : γ → γ'` a morphism `a(α) : A(α)(a(γ)) → a(γ')`, functorially;
- **substitution** is precomposition, which is strict.

Definitional equality is interpreted as equality of these data. That is
why a *definitional* irrelevance law needs strictly unique elements, not
just unique ones up to isomorphism.

- **Π, Σ, `Id`**: as in Hofmann–Streicher. `Id_A(a, b)` at `γ` is the
  hom-set `A(γ)(a(γ), b(γ))`, as a discrete groupoid. J's β holds strictly.
  Σ-η and Π-η hold strictly.
- **`Unit^l`, `Empty^l`, `+`, `Nat`**: the terminal, initial, coproduct and
  discrete-ℕ families. `Unit`-η is strict because the fibre has one object
  and one morphism. Level indexing is bookkeeping: each is the same family
  at every level.
- **`Vec`, `Fin`, `DVec`**: by recursion on the `Nat` component of the
  context. Since `ℕ` is discrete, the recursion is pointwise in `γ`, and
  the reductions of `wf-former-design.md` §1 and `iwf-former-design.md`
  §1.1 hold strictly. At a neutral length they are the family itself.
- **`Wf`, `IWf`, `W`**: initial algebras of the polynomial functors, taken
  fibrewise and split. The finitary ones (`Wf`, `IWf`) are ω-cocontinuous,
  so the initial algebra is the ω-colimit. `W`'s positions are a type, so
  it needs a transfinite colimit, which exists because `Gpd` is locally
  presentable and the functor is accessible. β holds by definition of the
  eliminator on the initial algebra. For `IWf`, the index is carried by the
  family over `I`, and `sup_i(a; cs)` lands in the fibre at `o(a)`, as in
  Dybjer's set model of inductive families.
- **Universes.**
  - `Ty 0` is the groupoid of κ₀-small **sets and bijections**.
  - `Ty (l+1)` is the groupoid of κ_{l+1}-small **groupoids and
    isomorphisms**, with κ₀ < κ₁ < … inaccessible.
  - `El` is the tautological family, which is split because it acts by the
    given bijection or isomorphism.
  - Each code former `TmNat`, `TmPi`, … is the functor that performs the
    corresponding construction. So `El(TmX(…)) = X(El …)` holds strictly,
    as Hofmann–Streicher do for their universe of sets.
  - `Ty l` is an object of `Ty (l+1)`, and `El(TmTy l) = Ty l` holds.
  - Every level-0 type former returns a set on sets, so `Ty 0` is closed
    under them. Level-`l+1` formers return groupoids, so `Ty (l+1)` is
    closed under them.
  - Heather has **no eliminator on `Ty l`**: the code recursors eliminate
    `□`, §4. So nothing forces the universe to be discrete.
- **`ΠΠ` (universe polymorphism) at `ω`**: the product over level
  assignments of the family at each assignment. It is a family not
  classified by any universe, as `ω` types are not.

---

## 3. The strict propositions: `sEq`, `sEmpty`, `Squash`

### 3.1 The construction

For a type `A` over `Γ` and terms `a, b : A`, let

```
Γ_{a~b} := { γ ∈ Γ | A(γ)(a(γ), b(γ)) ≠ ∅ }       (a full subgroupoid)
⟦sEq(A; a; b)⟧(γ) := 1 if γ ∈ Γ_{a~b}, else ∅       (1 = one object, identity only)
```

and similarly `⟦Squash A⟧(γ) := 1` if `A(γ)` has an object, else `∅`, and
`⟦sEmpty⟧ := ∅`.

**Lemma (these are types).** `Γ_{a~b}` is closed under isomorphism in `Γ`.
So `⟦sEq⟧` is a functor `Γ → Gpd`, sending every morphism to an identity.
It is strictly stable under substitution.

*Proof.* Take `α : γ → γ'` and `f : a(γ) → b(γ)` in `A(γ)`. Then
`b(α) ∘ A(α)(f) ∘ a(α)⁻¹ : a(γ') → b(γ')` is a morphism of `A(γ')`, since
`A(α)` is a functor and `a(α)`, `b(α)` are the sections' morphism
components. It is invertible because everything is a groupoid. So
`γ ∈ Γ_{a~b} ⇒ γ' ∈ Γ_{a~b}`, and conversely via `α⁻¹`. For a
substitution `σ : Δ → Γ`, the set `Δ_{a[σ]~b[σ]}` is `σ⁻¹(Γ_{a~b})` on the
nose: the sections at `δ` are `a(σδ)` and `b(σδ)`. The same argument
applies to `Squash`, replacing "a morphism between the two sections" by
"an object". ∎

In other words, the strict propositions are the unions of connected
components of the context: the "monomorphic" families.

### 3.2 The rules

- **Formation and conversion.** `sEq`'s type conversion compares
  endpoints, and equal interpretations give equal subgroupoids.
- **`srefl`.** `id_{a(γ)}` witnesses `γ ∈ Γ_{a~a}`.
- **Irrelevance at `sEq`, `sEmpty`, `Squash`.** A fibre has at most one
  object and only its identity, so any two sections are *equal*, not
  just isomorphic. This is exactly what a definitional law needs, and it
  is why an interpretation as a propositional truncation up to
  isomorphism would not do.
- **`elim_sEmpty`.** Over the empty fibre, anything goes.
- **`ElimSquash`.** The target `∥B(z)∥` is again of this form, so a section
  is only a *proof of non-emptiness* at each `γ`. No choice has to be
  natural. Where `A(γ)` has an object `x`, the case term gives
  `∥B(squash x)∥(γ) ≠ ∅`. β holds because both sides are the unique point.
- **Codes** `TmSEq`, `TmSEmpty`, `TmSquash` in `Ty 0` are the functors
  `γ ↦ 1 or ∅`, and `El` of them is the family above, strictly.
- **The nominal tag** `sEq(Nat; k; k)` is `1` everywhere.

### 3.3 Why this is not UIP by the back door

The only data a strict proposition carries is *whether* two things are
connected, which is a property of connected components. Mapping `Id` into
`sEq` (`toS`, by J) is fine: it forgets which morphism. What the removed
`transp` did was go back, from connectedness to a chosen morphism,
naturally in `Γ` and strictly `id` at `srefl`.

### 3.4 Sanity check: relevant `transp` fails, restricted `transp` holds

- **Relevant motive.** Take the context `X Y : Ty 0, e : sEq(Ty 0; X; Y)`.
  Its interpretation is the groupoid of pairs of *isomorphic* sets, with
  pairs of bijections `(α, β)` as morphisms. A term
  `transp(z. El z; X; Y; e; t) : El Y` for `t : El X` would be a family of
  functions `f_{X,Y} : X → Y`, natural in that groupoid:
  `f_{X',Y'} ∘ α = β ∘ f_{X,Y}`. At `X = Y = 2` with `α = id`, `β = swap`,
  this says `f = swap ∘ f`, and no function `2 → 2` satisfies it, since
  `swap` has no fixed point. So no relevant `transp` exists in the model,
  consistent with §1. The obstruction is the naturality demanded by `e`'s
  irrelevance, which is exactly what UIP encodes.
- **Strict motive.** When `P` is a strict proposition, a section of
  `P(b)` over `Γ_{a~b}` only has to exist. It does: `P(a(γ))` non-empty
  implies `P(b(γ))` non-empty, by the lemma's argument applied to `P`'s
  action along `f : a(γ) ≅ b(γ)` in the context extended by the index.
  So re-adding `transp` at strict motives keeps this model, and hence
  keeps UIP underivable.

---

## 4. DeLaM's layers, globals and `□`: by stratification

DeLaM has no published semantic model. Hu and Pientka's own argument is a
logical relation. This section is checked against the declarative rules
of the Coq formalization (`../Lean/delam/theories/Typing/Declarative.v`,
cited by rule name below); it is not mechanized. The review of
2026-09-30 is recorded at the end of the section.

### 4.1 The layer facts the construction uses

Each fact is a side condition of the cited rule, so none is an
assumption:

- **A global declared at layer `i'` is usable only at layers `i ≥ i'`**
  (`wft_gvar`, `wf_gvar`: premise `lle i' i`).
- **`□` and everything that eliminates it are layer M only.**
  `wf_boxT`, `wf_boxt`, `wf_letboxT`/`wf_letboxt`, `wf_elimT`/`wf_elimt`,
  and the meta-functions `wft_cpi`/`wft_tpi` all conclude at `lM`. No
  C- or D-layer rule mentions them.
- **Box contents are layer-C code** (`wf_boxT`: `Δ ⊢[lC] T`). `letbox`
  binds a **layer-C** global (`gdTy Δ lC l`, `gdTm Δ lC T l`). `TΠ` binds
  a **layer-D** type global (`gdTy Δ lD l`), and `CΠ` binds a context
  global (`gdCtx`).
- Hence **a layer-D global never occurs in code**: code is checked at
  `lC`, and `lle lD lC` is false. A layer-C global can occur in code, and
  that is how `letbox`'s body splices it.
- **Conversion at layer C is syntactic, up to level equivalence**
  (`static_code_eqty`, `static_code_eqtm`, `Typing/StaticCodeEq.v`). This
  is what makes `□` a discrete set. It is the declarative fact;
  `conv.rs`'s syntactic box comparison implements it.

### 4.2 The construction, in three stages

- **Stage 1: closed C/D.** Judgments at layers C and D with an empty
  global context contain no global, no `□` and no layer-M construct. So
  the fragment is ordinary type theory with Heather's formers, interpreted
  as in §2 and §3. Layer C is interpreted through its lifting to D
  (`Typing/Lifting.v`). The model identifies more code than C-conversion
  does, which is sound. As usual for interpreting derivations, the
  interpretation is defined on raw syntax (Streicher's partial
  interpretation), so it does not depend on the derivation chosen.
- **Stage 2: open C/D, under an environment.** An environment `ρ` for a
  global context `Ψ` assigns:
  - a level to each universe variable;
  - a closed syntactic context to each context global;
  - to each layer-C global, a pair: a closed code `c` of its type, and
    `c`'s stage-1 interpretation;
  - to each layer-D type global, a closed D-type up to D-conversion,
    with its stage-1 interpretation.

  A global's use at a local substitution `d` is its stage-1 value
  reindexed along `⟦d⟧`. `Inst(Ψ)`, the set of environments, is a set.
- **Stage 3: layer M under an environment.**
  - `□(Δ ⊢ T)` at `ρ` is the discrete groupoid of closed code of type
    `T[ρ]`, modulo level equivalence. `box t` at `ρ` is the syntax
    `t[ρ]`, which uses the syntax components of `ρ`.
  - A term of `□`-type in an M-context `Γ` is a section of a discrete
    family. It is therefore **constant on connected components** of
    `⟦Γ⟧ρ`.
  - `letbox u = t in t'` at an object `γ` is `t'` at the environment
    `(ρ, u ↦ t(γ))`, and at the same object. That object exists because
    `Γ` does not mention `u`, so the weakened context has the same
    interpretation. It is natural because `t(γ)` is constant along
    `Γ`'s morphisms.
  - Code recursors recurse on the syntax `t(γ)` in the same way, with β
    by definition.
  - `CΠ` and `TΠ` are products over context globals and over D-types up
    to conversion. `TΠ(U : (Δ ⊢ @l)). T @ l'` ranges over syntax, a
    countable set, so no size question arises, even though `l'` is
    independent of `l`. (No code former exists for `CΠ`/`TΠ`, so a
    product over semantic families would also do.)
  - Bodied globals are instantiated by their bodies.

**The obligation that ties the stages together** is the semantic global
substitution lemma:

```
⟦t⟧(ρ, u ↦ (c, ⟦c⟧)) = ⟦t⦃c/u⦄⟧ρ
```

together with its variants for context and type globals. It validates
`letbox`'s β (`eqtm_letboxT_beta`, `eqtm_letboxt_beta`) and the
meta-functions' β. It holds because the environment stores the syntax,
so every syntax-reading construct (`box`, the recursors) sees `c` on
both sides, while every semantic use of `u` sees `⟦c⟧`. The proof is by
induction on `t`, and it is the standard substitution lemma with one
syntactic case per construct that reads code.

### 4.3 Scope

The claim of this document is about the **empty global context**, or a
global context of definitions only. A module that postulates a global of
an empty type makes `Inst(Ψ)` empty and the interpretation vacuous. A
module that postulates UIP proves it. Neither says anything about the
rule set.

### 4.4 Review record (2026-09-30)

This is a self-review against the Coq rules, not an independent one. The
draft of this section was right in outline, and three things in it were
wrong or missing:

1. **"Conversion at `□` is syntactic" cited the implementation.** The
   declarative fact is Static Code (`StaticCodeEq.v`), and it is
   syntactic only **up to level equivalence**. `□` is code modulo level
   equivalence.
2. **The well-foundedness sentence** ("a global is interpreted as
   `⟦ρ(u)⟧`; closed code is interpreted first") hid two obligations. The
   environment must carry syntax and semantics together. And the semantic
   global substitution lemma above is what makes `letbox`'s β sound.
   Both are now explicit.
3. **Scope**: postulated globals were not excluded (§4.3).

It also added two facts the draft used without stating: sections of
`□`-types are constant on connected components, which `letbox` and the
recursors need to be natural; and environments include level
assignments. Nothing found contradicts the construction. What remains
unchecked is the substitution lemma's proof, which is routine but has not
been written out case by case.

---

## 5. UIP fails, and where it holds

At the empty context, `⟦Id^1(Ty 0; ⌜Bool⌝; ⌜Bool⌝)⟧` is the hom-set of
`Ty 0` from `2` to `2`, which is `{id, swap}`. `Id` over that is
`{*}` if the two morphisms are equal and `∅` otherwise. So
`⟦UIP₀⟧ ∋ s` would need `s(id, swap) ∈ ∅`. There is no such `s`, so
`UIP₀` has no closed term (soundness of the interpretation).

UIP *does* hold in the model at every type whose interpretation is a
discrete groupoid: `Nat`, first-order data, `□` code, and the strict
propositions. That matches what the syntax proves: Hedberg's theorem at
types with decidable equality. The model says nothing new there, and the
index-inversion tier 3 of `iwf-former-design.md` §8.3 (deletion only at
decidable index types) stays inside what the model validates.

Bonus remark, not load-bearing: `Ty 0` is a univalent universe of sets in
this model (Hofmann–Streicher's observation), so Heather's rule set is
consistent with univalence *for `Ty 0`*. `Ty (l+1)` is not univalent here:
its identities are isomorphisms of groupoids, not equivalences.

---

## 6. What is assumed

| piece | status |
|---|---|
| Π, Σ, `Id`, universe of sets, strict η and J | Hofmann–Streicher 1998 |
| `Ty (l+1)` as groupoids with isomorphisms, hierarchy by inaccessibles | routine extension, stated in §2 |
| `Unit`/`Empty`/`+`/`Nat`, `Vec`/`Fin`/`DVec` | routine: pointwise, and by recursion on discrete ℕ |
| `Wf`/`IWf` (finitary), `W` | initial algebras: ω-colimit for the finitary ones, accessibility for `W` |
| `ΠΠ` at `ω` | products over level assignments |
| strict propositions `sEq`/`sEmpty`/`Squash` | **new lemma, proved in §3.1, mechanized** (`NoUipComponents.v`: `conn_transport`, `sEq_subst`, `sec_irrelevant`, `ElimSquash`, `transp_strict`, `no_relevant_transp`, `no_uip0`) |
| DeLaM globals, `□`, code recursors, `CΠ`/`TΠ`, δ | **argued by stratification (§4)**; the layer facts it uses are side conditions of the Coq rules (§4.1); the semantic global substitution lemma is stated, not written out |

The mechanization states contexts as reflexive graphs (morphisms and
identities only) and fibres as groupoid data. None of the groupoid laws is
used, so the results hold for groupoids in particular. Strict propositions
are Coq's `SProp`, whose definitional irrelevance is exactly the strict
uniqueness the model provides. Sections of a strict family are then an
`SProp`, and their irrelevance is checked by conversion alone.

What would strengthen it:
- An independent review of §4, and the semantic global substitution
  lemma (§4.2) written out case by case. That lemma is now where the
  argument has the least slack. The layer-D type globals, flagged here
  before the review, turned out fine: they range over syntax, which is a
  countable set, and never occur in code (§4.1).
