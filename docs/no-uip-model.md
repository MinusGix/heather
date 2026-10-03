# UIP is not derivable without `transp`: a groupoid-model argument

Status: **paper argument, 2026-09-30**. §3 and the two counterexamples of
§3.4 and §5 are **mechanized** (`../Lean/delam/probes/NoUipComponents.v`,
closed under the global context). §4 is argued, and was self-reviewed
against the Coq formalization's rules the same day (§4.4). Once the
formalization had `Id` (its M11), `UIP₀` was stated there and the model's
`Id` was checked rule by rule against it (§4.5, §5.1). Once it had `+`
(its M12), `UIP₀` was restated at `⌜Bool⌝`, and Hedberg's theorem, the
positive prediction of §5.2, was proved in its syntax. The model's `J`,
in the formalization's Paulin-Mohring form, is **mechanized**
(`../Lean/delam/probes/NoUipJ.v`). It has not been independently
reviewed.
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
  Σ-η and Π-η hold strictly. `J` is Paulin-Mohring's, with the left
  endpoint fixed, as in the rules: at `γ`, `J(y p. M; c; u; e)` is `M`'s
  action on `c(γ)` along the morphism `(id_γ, e(γ)) : (γ, a(γ), id) →
  (γ, u(γ), e(γ))` of the motive's context `Γ.A.Id(a↑; y)` (§4.5).
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

### 4.2a The semantic global substitution lemma, written out

Notation follows the Coq formalization (`../Lean/delam/theories/Syntax/`).
- A global substitution `σ : Ψ ⇒ Ψ₀` maps each global `i` of `Ψ` to an
  object `σ i`, which is one of: `GId j` (another global), `GCtx Δ₀`,
  `GTy T` or `GTm t`. The objects are syntax over `Ψ₀`.
- `t⦃σ⦄` applies `σ`, and `gosubst o τ` applies `τ` inside an object.
- `gup σ` lifts `σ` under one global binder. `gsingle o` is `(o, id)`.
- A global's use carries a local substitution `d`: `gvar i d`,
  `tyGvar i d`, and a context global inside a context.

**Environments.** An environment `ρ ∈ Env(Ψ₀)` is a level assignment
together with a **closing substitution** `ρ̂`. Its objects have no global
variables other than definitions; levels are read through the assignment.
Definitions are the one exception because a well-formed substitution
must send a defined global to a defined one (`pdef`, `Term.v`, M9). So
`ρ̂` maps each definition to itself. A definition's use `gdef j b d`
carries its body `b` inline and is interpreted through it (case 9), so
definitions never need an environment entry. The
*semantic component* of a C/D global `i` is `s_ρ(i) := ⟦ρ̂ i⟧₁`, the
stage-1 interpretation of its closed syntax. For a layer-D type global,
`ρ̂ i` is a representative of its conversion class. Stage-1 soundness of
D-conversion makes `s_ρ(i)` independent of which representative.

**Composite environment.** For `σ : Ψ ⇒ Ψ₀` and `ρ ∈ Env(Ψ₀)`, define
`ρ·σ ∈ Env(Ψ)` by `(ρ·σ)^ i := gosubst (σ i) ρ̂`, with the same level
assignment. It is again closing. It is well-typed when `σ` and `ρ` are,
by the global substitution theorem of the typing metatheory
(`gsubstitution`, `Typing/GSubstitution.v`).

**The clauses that read the environment.** Every other clause of the
partial interpretation is compositional: `⟦F(t₁,…)⟧ρ = F^sem(⟦t₁⟧ρ,…)`,
with local binders extending the local context and never the
environment. The rest are:

| construct | interpretation at `ρ` (object `γ` where relevant) |
|---|---|
| `gvar i d`, `tyGvar i d` | `s_ρ(i)` reindexed along `⟦d⟧ρ` |
| a context global `g` inside a context | the stage-1 context `⟦ρ̂ g⟧₁`, spliced |
| `boxT T`, `boxt t` | the code `T⦃ρ̂⦄` (resp. `t⦃ρ̂⦄`) modulo level equivalence |
| `letbox t' t` | `⟦t'⟧(ρ, c)` at `γ`, where `c := ⟦t⟧ρ(γ)` |
| `elimT rb t`, `elimt rb t` | recursion on the code `⟦t⟧ρ(γ)`; each branch `⟦b⟧(ρ, sub-codes)` |
| `clam t` / `capp t Δ` | `Δ₀ ↦ ⟦t⟧(ρ, Δ₀)` / `⟦t⟧ρ` at `Δ⦃ρ̂⦄` |
| `tlam t` / `tapp t A` | `[A₀] ↦ ⟦t⟧(ρ, A₀)` / `⟦t⟧ρ` at the class of `A⦃ρ̂⦄` |

**Syntactic facts**, checked in Coq (`Syntax/GSubst.v`, `Syntax/Commute.v`):

- **(S1) composition**, `gsubst_gsubst`: `t⦃σ⦄⦃τ⦄ = t⦃θ⦄` when
  `θ i = gosubst (σ i) τ`. In particular `t⦃σ⦄⦃ρ̂⦄ = t⦃(ρ·σ)^⦄`, by the
  definition of `ρ·σ`.
- **(S2) global after local substitution**, `gsubst_subst`:
  `t[d]⦃σ⦄ = t⦃σ⦄[d⦃σ⦄]`.
- **(S3) substituting a global**, which is the definition itself:
  `gsubst_tm`'s `gvar` clause is `ptm (σ u) (glsubst d σ)` (`Term.v`).
  - `(gvar i d)⦃σ⦄ = ptm (σ i) (d⦃σ⦄)`;
  - that is `c[d⦃σ⦄]` when `σ i = GTm c`;
  - and `gvar j (d⦃σ⦄)` when `σ i = GId j`.
- **(S4) lifting past a binder**, `gsubst_gren_all` with `gup`: renaming
  then substituting is substituting the composite. Hence
  `(ρ, c)·(gup σ) = (ρ·σ, c)`, checked pointwise: at `0` it is `c`, and
  at `i+1` it is `gosubst ((σ i)⟨↑⟩) (ρ̂, c) = gosubst (σ i) ρ̂`.
- **(S5) local substitution never enters a box**. `boxT T` and `boxt t`
  are closed in the local context, so `(boxT T)[d] = boxT T`. The global
  uses compose: `subst_gvar`, `(gvar i e)[d] = gvar i (e ∘ d)`.

**Semantic facts**, standard for split models:

- **(M1) local substitution lemma**: `⟦t[d]⟧ρ ≃ ⟦t⟧ρ` reindexed along
  `⟦d⟧ρ`. It is the usual induction (Hofmann, Streicher). The two new
  clauses are immediate: the global-variable case by (S5) and
  functoriality of reindexing, and the box case because a box's
  interpretation is constant.
- **(M2) closing lemma for C/D.** For a term `t` at layer C or D,
  `⟦t⟧ρ ≃ ⟦t⦃ρ̂⦄⟧₁`. *Proof.* By induction on `t`. C/D syntax has no
  global binders (`letbox`, `CΠ`, `TΠ` are M only, §4.1), so the only
  non-compositional case is a global. There,
  `⟦gvar i d⟧ρ = s_ρ(i)·⟦d⟧ρ = ⟦ρ̂ i⟧₁·⟦d⦃ρ̂⦄⟧₁`
  by the induction hypothesis on `d`. By (M1) at stage 1 that is
  `⟦(ρ̂ i)[d⦃ρ̂⦄]⟧₁`, which is `⟦(gvar i d)⦃ρ̂⦄⟧₁` by (S3). ∎

**Lemma (semantic global substitution).** For every raw type, term,
context or local substitution `t` over `Ψ`, every `σ : Ψ ⇒ Ψ₀` and every
`ρ ∈ Env(Ψ₀)`:

```
⟦t⦃σ⦄⟧ρ  ≃  ⟦t⟧(ρ·σ)          (Kleene equality)
```

*Proof.* By induction on `t`, for all `σ` and `ρ` at once.

1. **Compositional formers**: `Π`, `Σ`, `λ`, application, `Id`/`J`, `Nat`
   and its recursor, `W`/`Wf`/`IWf`, `Vec`/`Fin`/`DVec`, the universes
   and their codes, `El`, `sEq`/`srefl`, `Squash`, `sEmpty`, `+`, `Unit`,
   `ΠΠ`/`Λ`/`$`, and local variables. Global substitution commutes with
   the former syntactically: local binders are a separate namespace from
   globals, and `σ`'s objects enter only through a `d` (S3). The
   interpretation is `F^sem` of the parts. Apply the induction hypothesis
   componentwise. Levels are untouched by `σ`, and `ρ·σ` keeps `ρ`'s
   level assignment.
2. **A global, `σ i = GTm c`.** Its interpretation is
   `⟦(gvar i d)⦃σ⦄⟧ρ = ⟦c[d⦃σ⦄]⟧ρ` (S3), which is
   `⟦c⟧ρ·⟦d⦃σ⦄⟧ρ` (M1). By (M2) on `c`, which is well-typed at layer C,
   `⟦c⟧ρ = ⟦c⦃ρ̂⦄⟧₁ = ⟦(ρ·σ)^ i⟧₁ = s_{ρ·σ}(i)`. By the induction
   hypothesis on `d`, `⟦d⦃σ⦄⟧ρ = ⟦d⟧(ρ·σ)`. Together that is
   `⟦gvar i d⟧(ρ·σ)`. `tyGvar` with `σ i = GTy T` is the same, and so is
   a layer-D type global: its object is a D-type, and (M2) applies
   because C ⊆ D.
3. **A global, `σ i = GId j`.** Then `(gvar i d)⦃σ⦄ = gvar j (d⦃σ⦄)`, and
   `(ρ·σ)^ i = gosubst (GId j) ρ̂ = ρ̂ j`, so `s_{ρ·σ}(i) = s_ρ(j)`. Apply
   the induction hypothesis on `d`.
4. **A context global inside a context**, `σ g = GCtx Δ₀` or `GId j`: as
   cases 2 and 3, with `pctx` in place of `ptm` and the stage-1 context
   interpretation in place of the term one.
5. **`boxT T`, `boxt t`.** `⟦(boxT T)⦃σ⦄⟧ρ` is the code `T⦃σ⦄⦃ρ̂⦄`, which
   is `T⦃(ρ·σ)^⦄` by (S1), and that is `⟦boxT T⟧(ρ·σ)`. The equality is
   on the nose, so it also holds modulo level equivalence.
6. **`letbox t' t`.** The substitution goes under the binder:
   `(letbox t' t)⦃σ⦄ = letbox (t'⦃gup σ⦄) (t⦃σ⦄)`. At `γ`:
   - The scrutinee gives the code `c := ⟦t⦃σ⦄⟧ρ(γ)`, which is
     `⟦t⟧(ρ·σ)(γ)` by the induction hypothesis on `t`.
   - The body gives `⟦t'⦃gup σ⦄⟧(ρ, c)`, which is `⟦t'⟧((ρ, c)·(gup σ))`
     by the induction hypothesis on `t'`, with `σ := gup σ` and
     `ρ := (ρ, c)`.
   - That environment is `(ρ·σ, c)` by (S4), so the result is
     `⟦letbox t' t⟧(ρ·σ)` at `γ`.
   - The local context `Γ⟪S⟫` of the body denotes `⟦Γ⟧` under both
     environments. That is the lemma for the weakening renaming (the
     instance `σ := ↑`), and it holds on the same objects `γ`.
7. **`elimT rb t`, `elimt rb t`.** Both sides recurse on the same code,
   `⟦t⦃σ⦄⟧ρ(γ) = ⟦t⟧(ρ·σ)(γ)`, by the induction hypothesis on `t`.
   - Each branch lives under the global binders that name the sub-codes
     (`wrapG`). A branch `b` is interpreted at `(ρ, c̄)` on one side and
     at `(ρ·σ, c̄)` on the other. The binders give `b⦃gupⁿ σ⦄`, so the
     induction hypothesis with (S4), applied `n` times, equates the two.
   - The motives are the same. The recursion is defined by the same
     equations on the same code, so its values agree by induction on the
     code.
8. **`clam`/`capp`, `tlam`/`tapp`.**
   - The binders are as in case 6: `(ρ, Δ₀)·(gup σ) = (ρ·σ, Δ₀)`, and the
     same for a type class `[A₀]`.
   - For `capp t Δ`, the argument is `Δ⦃σ⦄⦃ρ̂⦄ = Δ⦃(ρ·σ)^⦄` by (S1).
   - For `tapp t A`, the argument is the class of
     `A⦃σ⦄⦃ρ̂⦄ = A⦃(ρ·σ)^⦄`, again by (S1).
   - The function part is the induction hypothesis.
9. **Bodied globals** (`gdef i b d`, M9). A well-formed `σ` sends `i` to
   a defined `GId j`, so `(gdef i b d)⦃σ⦄ = gdef j (b⦃σ⦄) (d⦃σ⦄)` (`pdef`).
   The interpretation ignores the name and uses the inline body: it is
   `⟦b⟧` reindexed along `⟦d⟧`. Apply the induction hypothesis to `b` and
   to `d`. ∎

**What it validates.**
- **`letbox`'s β** (`eqtm_letboxT_beta`, `eqtm_letboxt_beta`). The right
  side interprets as `⟦t'⦃gsingle c⦄⟧ρ = ⟦t'⟧(ρ·gsingle c)`, and
  `ρ·gsingle c = (ρ, c⦃ρ̂⦄)`. The left side interprets as
  `⟦t'⟧(ρ, ⟦box c⟧ρ)`, which is `⟦t'⟧(ρ, c⦃ρ̂⦄)`.
- **`CΠ`/`TΠ` β and η** (`eqtm_cbeta`, `eqtm_tbeta`, `eqtm_ceta`, `eqtm_teta`) the same way.
- **The recursors' β.** `redT` builds the reduct by global substitution
  of the sub-codes into the branch. The interpretation recurses with the
  sub-codes in the environment, and the lemma equates the two.
- **Global weakening** is the instance `σ := ↑` (a renaming, whose
  objects are `GId`s). It is used for the weakened local contexts in
  every global binder rule.

**What it rests on.**
- The Coq-checked syntax lemmas (S1)–(S5).
- The global substitution theorem of the typing, also in Coq: it
  keeps `ρ·σ` well-typed.
- (M1), the standard local substitution lemma of the split model. Its
  only new cases are immediate.
- Stage-1 soundness of D-conversion, used only to make `s_ρ` of a
  layer-D type global independent of the representative.

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
assignments. Nothing found contradicts the construction. The substitution
lemma, unchecked at the review, is now written out case by case (§4.2a).
Its syntactic half rests on lemmas checked in Coq. Its semantic half rests
on the standard local substitution lemma (M1).

### 4.5 The formal `Id` rules against the model (2026-09-30)

The formalization gained `Id` in its milestone M11
(`../Lean/delam/M11_DESIGN.md`). Each rule below is from `Declarative.v`;
each is checked against §2's clause.

- **Layers.** Formation, `refl`, `J`, the code `TmId` and their
  congruences hold at every layer but V (C, D, M). The two computation
  rules, `eqtm_J_beta` and `eqty_El_id`, hold at D and M only. So Static
  Code still holds with `Id` at C (it was extended in Coq: `sc_id`,
  `sc_idrefl`, `sc_code_id`, `sc_J`, `StaticCode.v`). The §4.1 fact that
  C-conversion is syntactic up to level equivalence is unchanged, and `□`
  stays discrete.
- **`wft_id`.** `⟦Id^l(A; a; b)⟧(γ)` is the discrete hom-set. Along
  `α : γ → γ'` it acts by `f ↦ b(α) ∘ A(α)(f) ∘ a(α)⁻¹`, which is §3.1's
  map, now keeping the morphism. It is κ_l-small because `A(γ)` is.
- **`wf_idrefl`.** `refl(γ) := id_{a(γ)}`. It is a section because
  `A(α)` preserves identities.
- **`wf_J`.** In the motive's context `Γ.A.Id(a↑; var 0)`, the pair
  `(id_γ, e(γ))` is a morphism from `(γ, a(γ), id)` to `(γ, u(γ), e(γ))`:
  - its `A` component `e(γ) : a(γ) → u(γ)` is the orientation of the
    rules' `Id(a↑; y)`, left endpoint `a`;
  - its `Id` component must satisfy the discrete fibre's equation
    `e(γ) ∘ id ∘ id⁻¹ = e(γ)`, which holds.

  `J(γ) := M(id_γ, e(γ))(c(γ))`. Its result type `M[u/y, e/p]` is `M`
  reindexed along `γ ↦ (γ, u(γ), e(γ))`, which is `lsingle2 u e`. The
  rule's extra premise (the motive context's `Id` entry is a type) is a
  presupposition, and the model needs nothing from it. Naturality in `γ`
  is Hofmann–Streicher's argument. For `α : γ → γ'`, the two composites
  `(id, e(γ')) ∘ (α, a(α))` and `(α, u(α)) ∘ (id, e(γ))` agree in `Γ.A`.
  That is `e`'s section condition `e(γ') = u(α) ∘ A(α)(e(γ)) ∘ a(α)⁻¹`,
  an equation because the `Id` fibres are discrete. They then agree in
  `Γ.A.Id` too, whose last component is an equation. So `J(α)` is
  `c(α)` transported by `M`'s functoriality.

  **Mechanized** in `../Lean/delam/probes/NoUipJ.v`, closed under the
  global context:
  - `IdF` is `Id(a↑; var 0)` as a split family over `Γ.A`;
  - `reflS` is `refl`;
  - `J` is a section of `M[u/y, e/p]`, with both functor laws;
  - `square` is the equation above;
  - `J_beta_ob` and `J_beta_hom` are β on the nose.

  - `J_stab_ob` and `J_stab_hom` are stability under a substitution
    `σ`: `J(M; c; u; e)[σ] = J(M[σ⁺⁺]; c[σ]; u[σ]; e[σ])`. `Id` and
    `refl` are stable by conversion.

  The groupoids there have sets of objects and morphisms, as here. The
  comprehensions are used only as category data.
- **`eqtm_J_beta`** (D, M). At `u = a` and `e = refl`, the morphism is the
  identity, and `M(id) = id` strictly because families are split. So
  `J = c` on the nose.
- **`wf_code_id`, `eqty_El_id`.**
  - At `Ty 0`, `El s(γ)` is a set, and the code denotes `1` or `∅`, a set.
  - At `Ty (l+1)`, it denotes a hom-set of a groupoid, which is a small
    discrete groupoid.
  - Along `α`, it acts by the induced bijection of hom-sets.
  - `El` of it is `Id` by definition of the code former, strictly.
- **Congruences** (`eqty_id`, `eqtm_idrefl`, `eqtm_J`, `eqtm_code_id`).
  The interpretations are functions of the components. Level
  annotations related by `lequiv` denote the same level under every
  assignment. `eqtm_idrefl` compares the carriers and the points, which is
  exactly the data of `id_{a(γ)}`.
- **No η at `Id`.** There is no such rule, and the model refutes it
  (§5). The formalization's algorithm identifies any two `refl`s at one
  `Id` type (`actmnf_refl`). That is admissible, not a rule: its
  soundness derives the declarative judgment from `eqtm_idrefl`, after
  inversion and `Id` injectivity. The model has to validate only the
  derivation, and it does.
- **The code recursor's four branches** (`t_Id`, `t'_Id`, `t_refl`,
  `t_J`). Stage 3 recurses on code syntax (§4.2). The branches add four
  clauses, and their β is the defining equation.
  - `t_J`'s motive sub-code lives in a context with an `Id` entry over two
    other sub-codes, `cvar ,, A ,, Id(A↑; a↑; var 0)`. That is a layer-C
    type global whose context mentions globals. The environment closes it
    like any other (§4.2a, S3).
  - Case 7 of §4.2a is unchanged: the branch sits under `wrapG`'s seven
    global binders and six local ones, the same pattern as the other
    branches.

Nothing found contradicts the construction.

---

## 5. UIP fails, and where it holds

At the empty context, `⟦Id^1(Ty 0; ⌜Bool⌝; ⌜Bool⌝)⟧` is the hom-set of
`Ty 0` from `2` to `2`, which is `{id, swap}`. `Id` over that is
`{*}` if the two morphisms are equal and `∅` otherwise. So
`⟦UIP₀⟧ ∋ s` would need `s(id, swap) ∈ ∅`. There is no such `s`, so
`UIP₀` has no closed term (soundness of the interpretation).

### 5.1 In the formalization

The formalization states `UIP₀` as written above, with
`⌜Bool⌝ := ⌜Unit⌝ + ⌜Unit⌝` (`UIP0`,
`../Lean/delam/theories/Validity/Uip.v`, since its M12). Before it had
`+` it took `⌜Nat⌝` for `⌜Bool⌝` (`UIP0_nat`). This changes nothing:
`ℕ` has non-identity bijections, and one suffices.

Checked in Coq, all closed under the global context:
- `UIP0_wf`, `UIP0_nat_wf`: both are closed types at every layer but V,
  in any global context. `uip_pt_wf` is the same for any carrier and
  endpoints.
- `no_uip0`, `no_uip0_nat` (probe): the model's interpretations at the
  empty context, `∀ p q : bij Bool Bool. p = q` and `∀ p q : bij ℕ ℕ. p = q`,
  are refuted by `swap` and by the transposition of `0` and `1`.
- `uip_unit_wf`: UIP at `Unit` is *proved in the syntax*. The model
  predicts this, since `Unit`'s fibre is discrete. The proof is two `J`s,
  and `Unit` enters only through its η, which turns the motive's variable
  endpoint back into `tt`. At `Ty 0` the same step would need
  `y ≅ ⌜Nat⌝` for a variable `y : Ty 0`. No rule gives that, since
  `Ty l` has no eliminator and no η. That is the freedom the model's
  non-discrete universe uses.
- `closed_id_uip`: any two **closed** proofs of an `Id` type are
  convertible, by canonicity (both compute to `refl`) and `Id`
  injectivity. This is UIP as a metatheorem for closed terms. The model
  agrees: a closed proof denotes an identity morphism. So the
  counterexample is the semantic `swap`, which no closed term denotes.
  `UIP₀` fails because its `Π` ranges over all elements of the fibre, not
  over closed syntax.

### 5.2 Where UIP holds

UIP *does* hold in the model at every type whose interpretation is a
discrete groupoid: `Nat`, first-order data, `□` code, and the strict
propositions. That matches what the syntax proves: Hedberg's theorem at
types with decidable equality. The formalization proves it
(`../Lean/delam/theories/Validity/Hedberg.v`, closed under the global
context): as a schema over any carrier with a decider, as one closed
term of `Π(a : Ty l). DecEq(El a) → UIP(El a)`, at `Bool`, whose
decider uses `Unit`-η on the diagonal and a large elimination into
`Ty l` off it, and at `Nat`, whose decider is a double `natrec`, with
`succ`-injectivity through `pred` and `0 ≠ succ` by the same large
elimination. The model says nothing new there, and the
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
| Π, Σ, `Id`, universe of sets, strict η and J | Hofmann–Streicher 1998; `Id` and Paulin-Mohring `J`, with strict β and stability under substitution, **mechanized** (`NoUipJ.v`) |
| `Ty (l+1)` as groupoids with isomorphisms, hierarchy by inaccessibles | routine extension, stated in §2 |
| `Unit`/`Empty`/`+`/`Nat`, `Vec`/`Fin`/`DVec` | routine: pointwise, and by recursion on discrete ℕ |
| `Wf`/`IWf` (finitary), `W` | initial algebras: ω-colimit for the finitary ones, accessibility for `W` |
| `ΠΠ` at `ω` | products over level assignments |
| strict propositions `sEq`/`sEmpty`/`Squash` | **new lemma, proved in §3.1, mechanized** (`NoUipComponents.v`: `conn_transport`, `sEq_subst`, `sec_irrelevant`, `ElimSquash`, `transp_strict`, `no_relevant_transp`, `no_uip0`) |
| `Id` as formalized (M11: every layer but V, Paulin-Mohring `J`, code, four recursor branches) | **checked rule by rule, §4.5**; `UIP0` stated at `⌜Bool⌝` (M12) and well-formed in Coq, its interpretation refuted in the probe, the model's positive predictions checked in Coq (§5.1), Hedberg's theorem proved in the syntax (§5.2) |
| DeLaM globals, `□`, code recursors, `CΠ`/`TΠ`, δ | **argued by stratification (§4)**; the layer facts it uses are side conditions of the Coq rules (§4.1); the semantic global substitution lemma is written out (§4.2a), its syntactic half on Coq-checked lemmas |

The mechanization states contexts as reflexive graphs (morphisms and
identities only) and fibres as groupoid data. None of the groupoid laws is
used, so the results hold for groupoids in particular. Strict propositions
are Coq's `SProp`, whose definitional irrelevance is exactly the strict
uniqueness the model provides. Sections of a strict family are then an
`SProp`, and their irrelevance is checked by conversion alone.

What would strengthen it:
- An independent review of §4, including the substitution lemma
  (§4.2a). The lemma's semantic half is where any remaining slack is:
  (M1) is taken as standard, and the partial interpretation's full
  clause list is only summarized in §2 and §4.2a. The layer-D type globals, flagged here
  before the review, turned out fine: they range over syntax, which is a
  countable set, and never occur in code (§4.1).
