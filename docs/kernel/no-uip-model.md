# UIP is not derivable without `transp`: a groupoid-model argument

Status: **paper argument, 2026-09-30**. §3 and the two counterexamples of
§3.4 and §5 are **mechanized** (`heather-coq/probes/NoUipComponents.v`,
closed under the global context). §4 is argued, and was self-reviewed
against the Coq formalization's rules the same day (§4.4). Once the
formalization had `Id` (its M11), `UIP₀` was stated there and the model's
`Id` was checked rule by rule against it (§4.5, §5.1). Once it had `+`
(its M12), `UIP₀` was restated at `⌜Bool⌝`, and Hedberg's theorem, the
positive prediction of §5.2, was proved in its syntax. The model's `J`,
in the formalization's Paulin-Mohring form, is **mechanized**
(`heather-coq/probes/NoUipJ.v`). It has not been independently
reviewed.
Owed by `docs/kernel/iwf-former-design.md` §12.3 before that rule set freezes.
**Independent review of §4: `docs/kernel/no-uip-model.md` (2026-10-16).**
It found three rules the interpretation as written did not validate
(R1–R3, each with a local fix) and four missing steps (R4–R7). **All
seven are applied (2026-10-17, §4.4a)**, and the two lemmas the review
suggested mechanizing are checked in Coq: the `□` fibres' invariance under
D-conversion (`heather-coq/theories/Typing/BoxFibre.v`) and `unf`'s
idempotence (`unf_idem`, `heather-coq/theories/Syntax/Unfold.v`).
The rule set in question is the revised one: `docs/kernel/sprop-design.md` with
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
(`heather-coq/probes/UipProbe.v`: `sEq` irrelevance, `transp` into any
motive, and β at `srefl`, even as a propositional equation). Any model of
this document's kind therefore *cannot* validate that `transp`. §3.4 shows
where it fails, as a sanity check on the construction. It also shows that
`transp` *restricted to strict motives* is validated, so re-adding that
restricted form stays UIP-free, as `docs/kernel/iwf-former-design.md` §7 claims.

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
of the Coq formalization (the `heather-coq` repository,
`theories/Typing/Declarative.v`, cited by rule name below). Two of its
lemmas are mechanized there (the `□` fibres' invariance and `unf`'s
idempotence, §4.2); the rest is argued. The self-review of 2026-09-30 and
the independent review of 2026-10-16 are recorded at the end of the
section (§4.4, §4.4a).

### 4.1 The layer facts the construction uses

Each fact is a side condition of the cited rule, so none is an
assumption:

- **A global declared at layer `i'` is usable only at layers `i ≥ i'`**
  (`wft_gvar`, `wf_gvar`: premise `lle i' i`).
- **`□` and everything that eliminates it are layer M only.**
  `wf_boxT`, `wf_boxt`, `wf_letboxT`/`wf_letboxt`, `wf_elimT`/`wf_elimt`,
  and the meta-functions `wft_cpi`/`wft_tpi` all conclude at `lM`. No
  C- or D-layer rule mentions them.
- **Box contents are layer-C code** (`wf_boxT`: `Δ ⊢[lC] T`). A box's
  **context and type are checked at D** (`wf_boxT`, `wf_boxt`,
  `wft_CTrm`: `Δ ⊢[lD]`, `Δ ⊢[lD] T`). That is the layer where a
  C-judgment's types live (`typeof lC = lD`, `Context.v`).
- **The global binders.** `letbox` binds a **layer-C** global
  (`gdTy Δ lC l`, `gdTm Δ lC T l`). `TΠ` binds a **layer-D** type global
  (`gdTy Δ lD l`), and `CΠ` binds a context global (`gdCtx`). The code
  recursors' branches bind globals for the sub-codes (`brDecls`,
  `Typing/RecSpec.v`), and two of them are of new kinds:
  - branch 4 (`t_x`) binds `U_T : (g ⊢ @ℓ)` at **layer D** and
    `u_x : (g ⊢ U_T @ℓ)` at **layer V**;
  - branch 11 (`t_λ`) binds `U_T : (g, x : U_S ⊢ @ℓ')` at **layer D**.
- **The level binders.** `UΠ` and `Λ` bind level variables (`wft_upi`,
  `wf_ulam`), and so do the recursors' branches (`bindU`). Their bodies
  live in the universe-weakened scope `gctx_uwk n G`, and code inside
  them can mention the bound levels: `Λℓ. box(Ty ℓ)` is well typed.
- Hence **a layer-D global never occurs in code itself**: code is
  checked at `lC`, and `lle lD lC` is false. It **can occur in the
  context and type of code**, which are checked at D. So the `□` fibres
  depend on D-globals, and that is why §4.2 takes the meta-functions'
  products over conversion classes. A layer-C global can occur in code,
  and that is how `letbox`'s body splices it.
- **A definition can occur in code.** `wf_gdef` needs only `lle lC i`,
  and there is no δ at C (`eqtm_delta` requires `compt i`). So
  `box(gdef u b d)` is closed code that no recursor branch matches: M9
  leaves it stuck (`whne_elimt_gdef`, `stuck_rec_wf`,
  `Validity/DefStuck.v`).
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
  A definition `gdef u b d` is interpreted through its inline body, as
  `b` reindexed along `d`.
- **Stage 2: open C/D, under an environment.** An environment
  `ρ = (v, ρ̂)` for a global context `Ψ` is a valuation `v` of the
  universe variables together with a closing substitution `ρ̂` (§4.2a).
  `ρ̂` assigns:
  - to each context global, a closed D-context, a representative of its
    class up to `[⊢[lD] Δ ≅ Δ']`;
  - to each layer-C or layer-V global, a closed code of its type;
  - to each layer-D type global, a closed D-type, a representative of its
    class up to D-conversion.

  Every entry is **level-closed** (each level variable replaced by the
  numeral `v` gives it, written `⌜v⌝`) and **unfolded** (in the image of
  M9's `unf`, `Syntax/Unfold.v`, so it mentions no definition). A
  global's semantic component is the stage-1 interpretation of its entry,
  and its use at a local substitution `d` is that reindexed along `⟦d⟧`.
  `Inst(Ψ)`, the set of environments, is a set.
- **Stage 3: layer M under an environment.**
  - `□(Δ ⊢ T)` at `ρ` is the discrete groupoid of **well-typed**,
    global-closed, level-closed, unfolded code `c` of type `T[ρ]` **in
    the local context `Δ[ρ]`**: code is closed in globals, not in local
    variables. The interpretation reads the typing judgment of the empty
    global context. That is harmless, since it is a set, and it makes the
    recursors' inversions available. On closed levels `≡ₗ` is equality,
    so "modulo level equivalence" adds nothing.
  - **The fibres depend on `Δ[ρ]`, `T[ρ]` and the level only up to
    D-conversion and level equivalence.** This is mechanized
    (`heather-coq`, `Typing/BoxFibre.v`): `box_fibre_ty_iff` along
    `eqty_CTyp`'s premises, and `box_fibre_tm_iff` along `eqty_CTrm`'s.
    The reason is that a C-judgment's types live at D, so `wf_conv` at C
    converts at D, and context conversion (`ctxconv_tm`,
    `Typing/CtxConv.v`) does the rest. So `eqty_CTyp`/`eqty_CTrm` hold,
    and so do the representative-independence lemma's fibre cases
    (§4.2a, (M3)).
  - `box t` at `ρ` is the code `unf(t⦃ρ̂⦄)[⌜v⌝]ᵤ`: the syntax under `ρ`'s
    syntax components, unfolded, with levels evaluated. So
    `box(gdef u b d)` and `box(b[d])` denote the same point. The model
    identifies more code than C-conversion does, which is sound.
  - A term of `□`-type in an M-context `Γ` is a section of a discrete
    family. It is therefore **constant on connected components** of
    `⟦Γ⟧ρ`.
  - `letbox u = t in t'` at an object `γ` is `t'` at the environment
    `(ρ, u ↦ t(γ))`, and at the same object. That object exists because
    `Γ` does not mention `u`, so the weakened context has the same
    interpretation. It is natural because `t(γ)` is constant along
    `Γ`'s morphisms.
  - **Code recursors recurse on typed code.** At `γ` the scrutinee is a
    code `t(γ)` of the fibre. Each step reads a typed sub-code by
    C-inversion, at the context and index that `redT`/`redt` give it, and
    binds it in the environment for the branch. The reducts' typing
    (`rec_red_typed`, `Validity/RecReduct.v`, which types the pieces by
    inverting the code's C-typing) keeps the recursion inside the fibres.
    It is total on typed, global-closed, unfolded C-code, since every head
    is one of the 61 branches (checked against the `tm`/`ty`
    constructors) and no `gdef` is left. β holds by definition. Two
    branches read more than the code:
    - **`t_x`** binds a layer-D type and a layer-V variable (§4.1). The
      type is the variable's type in the fibre's context, the variable is
      the code itself.
    - **`t_λ`** binds the codomain `U_T`. `lam` stores no codomain, and
      `redt` takes it from the index only when that is syntactically a
      `Π` (`match T with tyPi _ _ _ B => … | _ => None`, `Recursor.v`).
      The model cannot copy that: the index may be D-convertible to a `Π`
      without being one (`El (tmPi …)`, or a D-global whose
      representative is not a `Π`), and (M3) forbids reading its syntax.
      So the model takes `U_T` to be the class of `B`, where `T ≅ Π A B`
      at D. Such a `B` exists by inversion of the C-typed `lam` and
      `wf_conv`, and it is unique up to D-conversion by `decl_pi_inj`
      (`Validity/DeclConsequencesP.v`). The model therefore computes
      where the syntax is stuck, which is sound.

    The model also computes `elim(box(u^δ))`, which the syntax leaves
    stuck. That is consistent with M9's `stuck_rec_not_numeral`, since the
    model may identify more than the syntax.
  - `CΠ` and `TΠ` are products over **classes**: `CΠ` over closed
    D-contexts up to `[⊢[lD] Δ ≅ Δ']`, `TΠ` over closed D-types up to D
    conversion. Environments store a representative, and (M3) makes the
    choice irrelevant. `TΠ(U : (Δ ⊢ @l)). T @ l'` ranges over classes of
    syntax, a countable set, so no size question arises, even though
    `l'` is independent of `l`. (No code former exists for `CΠ`/`TΠ`, so
    a product over semantic families would also do.)
  - Bodied globals are instantiated by their bodies.

**The obligation that ties the stages together** is the semantic global
substitution lemma:

```
⟦t⟧(ρ, u ↦ c) = ⟦t⦃c/u⦄⟧ρ
```

together with its variants for context and type globals. It validates
`letbox`'s β (`eqtm_letboxT_beta`, `eqtm_letboxt_beta`) and the
meta-functions' β. It holds because the environment stores the syntax,
so every syntax-reading construct (`box`, the recursors) sees `c` on
both sides, while every semantic use of `u` sees `⟦c⟧`. The proof is by
induction on `t`, and it is the standard substitution lemma with one
syntactic case per construct that reads code. Its companion for levels,
the semantic universe substitution lemma, validates `ΠΠ`'s β and η
(§4.2a, "What it validates").

### 4.2a The semantic global substitution lemma, written out

Notation follows the Coq formalization (`heather-coq`,
`theories/Syntax/`).
- A global substitution `σ : Ψ ⇒ Ψ₀` maps each global `i` of `Ψ` to an
  object `σ i`, which is one of: `GId j` (another global), `GCtx Δ₀`,
  `GTy T` or `GTm t`. The objects are syntax over `Ψ₀`.
- `t⦃σ⦄` applies `σ`, and `gosubst o τ` applies `τ` inside an object.
- `gup σ` lifts `σ` under one global binder. `gsingle o` is `(o, id)`.
  `guwkn k σ` universe-weakens `σ`'s objects past `k` level binders.
- `t[φ]ᵤ` applies a level substitution `φ`, and `gousubst o φ` applies
  it inside an object.
- A global's use carries a local substitution `d`: `gvar i d`,
  `tyGvar i d`, and a context global inside a context.

**Environments.** An environment `ρ = (v, ρ̂) ∈ Env(Ψ₀)` is a valuation
`v` of the level variables together with a **closing substitution** `ρ̂`.
Write `⌜v⌝` for the level substitution sending each level variable to the
numeral `v` gives it. `ρ̂`'s objects:
- have no global variables;
- are **level-closed** (fixed by every level substitution);
- are **unfolded**: `unf_o (ρ̂ i) = ρ̂ i`, so they mention no definition;
- are **layer-correct**: free of layer-M syntax, and of the binding's
  sort (a code for a C- or V-global, a D-type for a D type global, a
  D-context for a context global).

Definitions need no entry. A definition's use `gdef j b d` carries its
body `b` inline and is interpreted through it (case 9). The *semantic
component* of a global `i` is `s_ρ(i) := ⟦ρ̂ i⟧₁`, the stage-1
interpretation of its closed syntax. For a context global or a layer-D
type global, `ρ̂ i` is a representative of its class, and (M3) below makes
everything independent of which representative.

**Composite environment.** For `σ : Ψ ⇒ Ψ₀` and `ρ = (v, ρ̂) ∈ Env(Ψ₀)`,
define `ρ·σ := (v, (ρ·σ)^)` with

```
(ρ·σ)^ i := unf_o (gosubst (σ i) ρ̂) [⌜v⌝]ᵤ
```

It is again closing, level-closed and unfolded (`unf_gfree`, and `unf`
commutes with level substitution, `unf_usubst`). It is layer-correct when
`σ` is (below). It is well-typed when `σ` and `ρ` are, by the global
substitution theorem of the typing metatheory (`gsubstitution`,
`Typing/GSubstitution.v`), together with `unfolding` (`Typing/Unfold.v`)
and level substitution.

**The clauses that read the environment.** Every other clause of the
partial interpretation is compositional: `⟦F(t₁,…)⟧ρ = F^sem(⟦t₁⟧ρ,…)`,
with local binders extending the local context and never the
environment. Level binders (`UΠ`, `Λ`, `bindU`) extend `v` only: `ρ̂` is
level-closed, so it needs no weakening. The rest are:

| construct | interpretation at `ρ = (v, ρ̂)` (object `γ` where relevant) |
|---|---|
| `gvar i d`, `tyGvar i d` | `s_ρ(i)` reindexed along `⟦d⟧ρ` |
| a context global `g` inside a context | the stage-1 context `⟦ρ̂ g⟧₁`, spliced |
| `boxT T`, `boxt t` | the code `unf(T⦃ρ̂⦄)[⌜v⌝]ᵤ` (resp. `unf(t⦃ρ̂⦄)[⌜v⌝]ᵤ`) |
| `letbox t' t` | `⟦t'⟧(ρ, c)` at `γ`, where `c := ⟦t⟧ρ(γ)` |
| `elimT rb t`, `elimt rb t` | recursion on the typed code `⟦t⟧ρ(γ)` (§4.2 stage 3); each branch `⟦b⟧(ρ, sub-codes)` |
| `clam t` / `capp t Δ` | `[Δ₀] ↦ ⟦t⟧(ρ, Δ₀)` / `⟦t⟧ρ` at the class of `unf(Δ⦃ρ̂⦄)[⌜v⌝]ᵤ` |
| `tlam t` / `tapp t A` | `[A₀] ↦ ⟦t⟧(ρ, A₀)` / `⟦t⟧ρ` at the class of `unf(A⦃ρ̂⦄)[⌜v⌝]ᵤ` |

**Syntactic facts**, checked in Coq (`Syntax/GSubst.v`, `Syntax/Commute.v`,
`Syntax/Universe.v`, `Syntax/Unfold.v`):

- **(S1) composition**, `gsubst_gsubst`: `t⦃σ⦄⦃τ⦄ = t⦃θ⦄` when
  `θ i = gosubst (σ i) τ`.
- **(S2) global after local substitution**, `gsubst_subst`:
  `t[d]⦃σ⦄ = t⦃σ⦄[d⦃σ⦄]`.
- **(S3) substituting a global**, which is the definition itself:
  `gsubst_tm`'s `gvar` clause is `ptm (σ u) (glsubst d σ)` (`Term.v`).
  - `(gvar i d)⦃σ⦄ = ptm (σ i) (d⦃σ⦄)`;
  - that is `c[d⦃σ⦄]` when `σ i = GTm c`;
  - and `gvar j (d⦃σ⦄)` when `σ i = GId j`.
- **(S4) lifting past a binder**, `gsubst_gren_all` with `gup`: renaming
  then substituting is substituting the composite. Hence
  `(ρ, c)·(gup σ) = (ρ·σ, c)`, checked pointwise: at `0` it is `c`
  (which is already level-closed and unfolded), and at `i+1` it is the
  normal form of `gosubst ((σ i)⟨↑⟩) (ρ̂, c) = gosubst (σ i) ρ̂`.
- **(S4u) lifting past a level binder**, `guwkn_gosubst`:
  `guwkn k θ = gosubst (guwkn k σ ·) (guwkn k τ)` when
  `θ = gosubst (σ ·) τ`. On the semantic side, `guwkn k ρ̂ = ρ̂`, since
  `ρ̂` is level-closed.
- **(S5) local substitution never enters a box**. `boxT T` and `boxt t`
  are closed in the local context, so `(boxT T)[d] = boxT T`. The global
  uses compose: `subst_gvar`, `(gvar i e)[d] = gvar i (e ∘ d)`.
- **(S6) levels after globals**, `usubst_gsubst` (`Universe.v`):
  `t⦃σ⦄[φ]ᵤ = t[φ]ᵤ⦃gousubst (σ ·) φ⦄`. With level substitutions
  composing (`usubst_usubst`) and evaluating (`leval_lvsubst`,
  `Level.v`).
- **(S7) unfolding commutes**, `unf_gsubst`, `unf_usubst`, `unf_subst`:
  `unf(t⦃σ⦄) = unf(t)⦃unf_o ∘ σ⦄`, `unf(t[φ]ᵤ) = unf(t)[φ]ᵤ`,
  `unf(t[d]) = unf(t)[unf d]`. And **`unf` is idempotent**,
  `unf_idem`/`unf_idem_ty`/`unf_idem_ctx`/`unf_o_idem` (mechanized for
  this section, `Syntax/Unfold.v`), so an unfolded entry is its own
  normal form.

**Semantic facts**, standard for split models. They are proved in this
order, because each one's binder cases use the ones before it:

- **(R) global renaming.** `⟦t⦃ξ⦄⟧ρ = ⟦t⟧(ρ∘ξ)` for a global renaming
  `ξ`. All its objects are `GId`s, so only the lemma's cases 3, 4 and 9
  occur, and (M1) is never used. Its binder cases are (S4) for renamings.
  The instance `ξ := ↑` is `⟦t⦃↑⦄⟧(ρ, c) = ⟦t⟧ρ`.
- **(U) universe renaming**, for `uwk d`: the same induction. Under
  level-closed environments it is the observation that a level-closed
  object is fixed by universe renaming.
- **(M1) local substitution lemma**: `⟦t[d]⟧ρ ≃ ⟦t⟧ρ` reindexed along
  `⟦d⟧ρ`. It is the usual induction (Hofmann, Streicher). Local
  substitution goes under every global and level binder (`subst_tm`,
  `Term.v`): `letboxT`/`letboxt` and `bindG` substitute `t'[gwk d]`,
  `clam`/`tlam` substitute under `gwk d`, `ulam` and `bindU` under
  `uwk d` (resp. `uwkn n d`), and `bindL` under `llift d`. Those cases
  use (R) at `↑` (`⟦gwk d⟧(ρ, c) = ⟦d⟧ρ`) and (U). The two new clauses
  are then immediate: the global-variable case by (S5) and functoriality
  of reindexing, and the box case because a box's interpretation is
  constant.
- **(M2) closing lemma for M-free syntax.** For raw syntax `t` free of
  layer-M constructs, `⟦t⟧ρ ≃ ⟦unf(t⦃ρ̂⦄)[⌜v⌝]ᵤ⟧₁`. *Proof.* By induction
  on `t`. M-free syntax has no global binders (`letbox`, `CΠ`, `TΠ` and
  the recursors are M only, §4.1), so the non-compositional cases are a
  global and a definition. For a global,
  `⟦gvar i d⟧ρ = s_ρ(i)·⟦d⟧ρ = ⟦ρ̂ i⟧₁·⟦unf(d⦃ρ̂⦄)[⌜v⌝]ᵤ⟧₁`
  by the induction hypothesis on `d`. By (M1) at stage 1 that is
  `⟦(ρ̂ i)[unf(d⦃ρ̂⦄)[⌜v⌝]ᵤ]⟧₁`, which is `⟦unf((gvar i d)⦃ρ̂⦄)[⌜v⌝]ᵤ⟧₁`
  by (S3), (S7) and `usubst_subst` (level substitution commutes with local
  substitution), since `ρ̂ i` is level-closed and unfolded. For
  `gdef j b d`, both sides interpret the body: stage 1 reads `gdef`
  through it, and `unf` replaces it by `b[d]`. In the compositional cases
  the level annotations agree, since `⟦l⟧v = ⟦l[⌜v⌝]ᵤ⟧` (`leval_lvsubst`). ∎ It covers layer-V globals too: their
  entries are codes, like a C-global's.
- **(M3) representative independence.** If `ρ` and `ρ'` agree on levels
  and on C- and V-globals, and their context and layer-D type entries are
  pairwise D-convertible, then `⟦t⟧ρ ≃ ⟦t⟧ρ'` for every `t`, and the two
  interpretations of a context or type are the same family. The same
  holds when the two differ by unfolding an entry. *Proof*, by induction
  on `t`. A representative is read in four places, and each is
  invariant:
  1. **Through `s_ρ`**, by stage-1 soundness of D-conversion, and of
     context conversion for a context global. An unfolded entry has the
     same stage-1 interpretation, since stage 1 reads `gdef` through its
     body.
  2. **Through a `□` fibre.** The fibre is invariant under D-conversion
     of its context and type, and under level equivalence. This is
     **mechanized**: `box_fibre_ty_iff`, `box_fibre_tm_iff`
     (`Typing/BoxFibre.v`).
  3. **Through box values.** They do not read the representatives at all.
     `static_gsubst` (`Typing/GStatic.v`) is the syntactic form of this:
     C-code under substitutions that agree on static bindings is
     `≡ₗ`-equal, and neither `gdCtx` nor a layer-D binding is static.
  4. **Through the recursors' contexts and indices**, by induction on the
     code, with stage 3's reading of `t_λ`'s index up to D-conversion.
  ∎ Once (M3) holds, the products over classes are well defined, and
  `eqtm_capp`, `eqtm_tapp`, `eqty_CTyp`, `eqty_CTrm`,
  `eqtm_elimT`/`eqtm_elimt`, `eqtm_tlam` and `eqty_tpi` hold: each
  compares its annotations `Δ`, `T` at D only.

**Lemma (semantic global substitution).** For every raw type, term,
context or local substitution `t` over `Ψ`, every **layer-correct**
`σ : Ψ ⇒ Ψ₀` and every `ρ ∈ Env(Ψ₀)`:

```
⟦t⦃σ⦄⟧ρ  ≃  ⟦t⟧(ρ·σ)          (Kleene equality)
```

`σ` is layer-correct when each object for a V-, C- or D-global is free of
layer-M syntax, and each is of the binding's sort. A well-typed `σ` is
layer-correct by inversion, since a judgment at a layer below M uses no
M rule. Without the hypothesis, case 2 fails: stage 1 is undefined on a
`box` or `letbox` in `c`, while the left side, the stage-3
interpretation of `c`, may be defined.

*Proof.* By induction on `t`, for all `σ` and `ρ` at once.

1. **Compositional formers**: `Π`, `Σ`, `λ`, application, `Id`/`J`, `Nat`
   and its recursor, `W`/`Wf`/`IWf`, `Vec`/`Fin`/`DVec`, the universes
   and their codes, `El`, `sEq`/`srefl`, `Squash`, `sEmpty`, `+`, `Unit`,
   and local variables. Global substitution commutes with the former
   syntactically: local binders are a separate namespace from globals,
   and `σ`'s objects enter only through a `d` (S3). The interpretation
   is `F^sem` of the parts. Apply the induction hypothesis componentwise.
   **`ΠΠ`/`Λ`/`$`** are the same, except that `σ` goes under the level
   binder as `guwkn n σ`
   (`gsubst_ty (tyUPi n l T) σ = tyUPi n l (T⦃guwkn n σ⦄)`, and likewise
   for `ulam`). The body is interpreted at `(v·v', ρ̂)` on one side and
   at `(v·v', (ρ·σ)^)` on the other. The induction hypothesis at
   `guwkn n σ`, with (S4u) and `guwkn n ρ̂ = ρ̂`, equates them.
2. **A global, `σ i = GTm c`.** Its interpretation is
   `⟦(gvar i d)⦃σ⦄⟧ρ = ⟦c[d⦃σ⦄]⟧ρ` (S3), which is
   `⟦c⟧ρ·⟦d⦃σ⦄⟧ρ` (M1). By (M2) on `c`, which is M-free because `σ` is
   layer-correct, `⟦c⟧ρ = ⟦unf(c⦃ρ̂⦄)[⌜v⌝]ᵤ⟧₁ = ⟦(ρ·σ)^ i⟧₁ = s_{ρ·σ}(i)`.
   By the induction hypothesis on `d`, `⟦d⦃σ⦄⟧ρ = ⟦d⟧(ρ·σ)`. Together
   that is `⟦gvar i d⟧(ρ·σ)`. `tyGvar` with `σ i = GTy T` is the same,
   and so is a layer-D type global: its object is an M-free D-type.
3. **A global, `σ i = GId j`.** Then `(gvar i d)⦃σ⦄ = gvar j (d⦃σ⦄)`, and
   `(ρ·σ)^ i = unf_o (gosubst (GId j) ρ̂)[⌜v⌝]ᵤ = ρ̂ j`, since `ρ̂ j` is
   already level-closed and unfolded. So `s_{ρ·σ}(i) = s_ρ(j)`. Apply
   the induction hypothesis on `d`.
4. **A context global inside a context**, `σ g = GCtx Δ₀` or `GId j`: as
   cases 2 and 3, with `pctx` in place of `ptm` and the stage-1 context
   interpretation in place of the term one.
5. **`boxT T`, `boxt t`.** Write `θ i := gosubst (σ i) ρ̂`, so that
   `(ρ·σ)^ = (unf_o ∘ θ)[⌜v⌝]ᵤ`.
   - The left side is the code `unf(T⦃σ⦄⦃ρ̂⦄)[⌜v⌝]ᵤ = unf(T⦃θ⦄)[⌜v⌝]ᵤ`
     by (S1), which is `unf(T)⦃unf_o ∘ θ⦄[⌜v⌝]ᵤ` by (S7).
   - The right side is `unf(T⦃(ρ·σ)^⦄)[⌜v⌝]ᵤ
     = unf(T)⦃unf_o ∘ unf_o ∘ θ[⌜v⌝]ᵤ⦄[⌜v⌝]ᵤ` by (S7) and `unf_usubst`,
     which is `unf(T)⦃(unf_o ∘ θ)[⌜v⌝]ᵤ⦄[⌜v⌝]ᵤ` by idempotence.
   - By (S6) both are `unf(T)[⌜v⌝]ᵤ⦃…⦄`, at objects `(unf_o ∘ θ)[⌜v⌝]ᵤ`
     and `(unf_o ∘ θ)[⌜v⌝]ᵤ[⌜v⌝]ᵤ`. These are equal: the first is
     level-closed, so `[⌜v⌝]ᵤ` fixes it.

   The equality is on the nose.
6. **`letbox t' t`.** The substitution goes under the binder:
   `(letbox t' t)⦃σ⦄ = letbox (t'⦃gup σ⦄) (t⦃σ⦄)`. At `γ`:
   - The scrutinee gives the code `c := ⟦t⦃σ⦄⟧ρ(γ)`, which is
     `⟦t⟧(ρ·σ)(γ)` by the induction hypothesis on `t`.
   - The body gives `⟦t'⦃gup σ⦄⟧(ρ, c)`, which is `⟦t'⟧((ρ, c)·(gup σ))`
     by the induction hypothesis on `t'`, with `σ := gup σ` and
     `ρ := (ρ, c)`. `gup σ` is layer-correct, and `c` is a valid entry:
     a box value is level-closed and unfolded.
   - That environment is `(ρ·σ, c)` by (S4), so the result is
     `⟦letbox t' t⟧(ρ·σ)` at `γ`.
   - The local context `Γ⟪S⟫` of the body denotes `⟦Γ⟧` under both
     environments. That is (R) at `↑`, and it holds on the same
     objects `γ`.
7. **`elimT rb t`, `elimt rb t`.** Both sides recurse on the same code,
   `⟦t⦃σ⦄⟧ρ(γ) = ⟦t⟧(ρ·σ)(γ)`, by the induction hypothesis on `t`.
   - Each branch lives under the global binders that name the sub-codes
     (`wrapG`) and under its level binders (`bindU`). Branch `k` is
     instantiated through `gbsub k σ = gupⁿ (guwkn m σ)`, with
     `n = br_ng k` and `m = br_nu k` (`RecGSubst.v`). A branch `b` is
     interpreted at `(ρ, c̄)` on one side and at `(ρ·σ, c̄)` on the other,
     with `v` extended by the branch's levels. The induction hypothesis
     with (S4u) once and (S4) `n` times equates the two.
   - The motives are substituted too, under the same level binders, and
     agree by the induction hypothesis with (S4u).
   - The recursion is defined by the same equations on the same code,
     so its values agree by induction on the code. The contexts and
     indices it reads (`t_x`'s type, `t_λ`'s codomain class) are the
     same on both sides, by the induction hypothesis and (M3).
8. **`clam`/`capp`, `tlam`/`tapp`.**
   - The binders are as in case 6: `(ρ, Δ₀)·(gup σ) = (ρ·σ, Δ₀)`, and the
     same for a type class `[A₀]`.
   - For `capp t Δ`, the argument is the class of
     `unf(Δ⦃σ⦄⦃ρ̂⦄)[⌜v⌝]ᵤ = unf(Δ⦃(ρ·σ)^⦄)[⌜v⌝]ᵤ`, as in case 5.
   - For `tapp t A`, the argument is the class of
     `unf(A⦃σ⦄⦃ρ̂⦄)[⌜v⌝]ᵤ = unf(A⦃(ρ·σ)^⦄)[⌜v⌝]ᵤ`, as in case 5.
   - The function part is the induction hypothesis.
9. **Bodied globals** (`gdef i b d`, M9). `pdef` (`Term.v`) has two
   cases:
   - `σ i = GId j`: `(gdef i b d)⦃σ⦄ = gdef j (b⦃σ⦄) (d⦃σ⦄)`. The
     interpretation ignores the name and uses the inline body: it is
     `⟦b⟧` reindexed along `⟦d⟧`. Apply the induction hypothesis to `b`
     and to `d`.
   - any other object: `pdef` inlines the body,
     `(gdef i b d)⦃σ⦄ = b⦃σ⦄[d⦃σ⦄]`. (M1) with the induction hypothesis
     on `b` and `d` closes it.

   Neither case needs a hypothesis on `σ`. ∎

**What it validates.**
- **`letbox`'s β** (`eqtm_letboxT_beta`, `eqtm_letboxt_beta`). The right
  side interprets as `⟦t'⦃gsingle c⦄⟧ρ = ⟦t'⟧(ρ·gsingle c)`, and
  `ρ·gsingle c = (ρ, unf(c⦃ρ̂⦄)[⌜v⌝]ᵤ)`. The left side interprets as
  `⟦t'⟧(ρ, ⟦box c⟧ρ)`, which is the same environment, since
  `⟦box c⟧ρ = unf(c⦃ρ̂⦄)[⌜v⌝]ᵤ`.
- **`letbox`'s dependent motive.** `wf_letboxT` types the body at
  `M⟪S⟫[box(u^id)]`. That `⟦t'⟧(ρ, t(γ))(γ)` lands in `⟦M[t]⟧ρ(γ)` uses
  (R) on `M`, `⟦box(u^id)⟧(ρ, c) = c` (from `gvar 0 (lshift 0)`, (S3) at
  the identity substitution, and `c` being a normal form), and (M1).
  Naturality uses the morphism `(α, id_c)` of `Γ.□`.
- **`CΠ`/`TΠ` β and η** (`eqtm_cbeta`, `eqtm_tbeta`, `eqtm_ceta`,
  `eqtm_teta`) the same way, and their congruences by (M3).
- **The recursors' β.** `redT` builds the reduct by global substitution
  of the sub-codes into the branch. The interpretation recurses with the
  sub-codes in the environment, and the lemma equates the two. `redt`'s
  reduct passes the sub-code as it is, where the model passes its normal
  form; they agree by (M3)'s unfolding clause.
- **The recursors' congruences** (`eqtm_elimT`, `eqtm_elimt`), by (M3)
  for the annotations, and because C-convertible scrutinees denote the
  same code.
- **`ΠΠ`'s β and η** (`eqtm_ubeta`, `eqtm_ueta`). These are not
  consequences of the global lemma. They need its companion, the
  **semantic universe substitution lemma**
  `⟦t[φ]ᵤ⟧(v, ρ̂) = ⟦t⟧(⟦φ⟧v, ρ̂)`, by the same induction. Its box case:
  `unf(T[φ]ᵤ⦃ρ̂⦄)[⌜v⌝]ᵤ = unf(T⦃ρ̂⦄)[φ]ᵤ[⌜v⌝]ᵤ` by (S6), since `ρ̂` is
  level-closed, and that is `unf(T⦃ρ̂⦄)[⌜⟦φ⟧v⌝]ᵤ` by `usubst_usubst` and
  `leval_lvsubst`. Its global case is (S6). Without level evaluation in
  box values the rule fails: `(Λℓ. box(Ty ℓ)) $ [0] ≡ box(Ty 0)` would
  compare the code `Ty ℓ` with `Ty 0`, and `ℓ ≢ₗ 0`.
- **Global weakening** is the instance `σ := ↑` (a renaming, whose
  objects are `GId`s), i.e. (R). It is used for the weakened local
  contexts in every global binder rule.

**What it rests on.**
- The Coq-checked syntax lemmas (S1)–(S7).
- The global substitution theorem of the typing, also in Coq: it
  keeps `ρ·σ` well-typed.
- The `□` fibres' invariance under D-conversion, **mechanized**
  (`Typing/BoxFibre.v`), for (M3).
- (R), (U), (M1), (M2) and (M3), in that order. (M1) is the standard
  local substitution lemma of the split model, whose binder cases use (R)
  and (U).
- Stage-1 soundness of D-conversion and of context conversion, used for
  (M3)'s first item.

### 4.3 Scope

The claim of this document is about the **empty global context**, or a
global context of definitions only. Definitions are covered because box
values are unfolded (§4.2 stage 3), so a boxed definition and its
unfolding denote the same code, and the recursion never meets a `gdef`.
Dropping definitions from the scope would not be simpler: `unfolding`
(`Typing/Unfold.v`) gives derivability of the unfolded judgment in
`unf_G G`, not a derivation free of `gdef`, so the model would still have
to interpret intermediate `box(gdef …)` terms.

A module that postulates a global of an empty type makes `Inst(Ψ)` empty
and the interpretation vacuous. A module that postulates UIP proves it.
Neither says anything about the rule set.

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

### 4.4a Independent review record (2026-10-16), applied 2026-10-17

The independent review (`docs/kernel/no-uip-model.md`) found that the
interpretation as written did not validate three rules, each with a
concrete instance, and that four steps were asserted where an argument
was needed. All seven are applied above:

| | finding | where it is fixed |
|---|---|---|
| R1 | `box` ignored the level assignment, so `eqtm_ubeta` failed at `Λℓ. box(Ty ℓ)` | environments `(v, ρ̂)` with level-closed entries; box values evaluate levels; the semantic universe substitution lemma (§4.2, §4.2a "What it validates") |
| R2 | context and type globals were raw syntax, but `eqtm_capp` and its siblings relate D-convertible ones | `CΠ`/`TΠ` over classes; (M3) representative independence, its fibre case mechanized (`Typing/BoxFibre.v`) |
| R3 | a boxed `gdef` had no recursion clause | box values and entries are unfolded by `unf`; `unf`'s idempotence mechanized (`unf_idem`, `Syntax/Unfold.v`); §4.3 |
| R4 | the recursor's branches bind layer-D and layer-V globals, and `t_λ` reads the index | V-globals in environments; recursion on typed code; `t_λ`'s codomain up to D-conversion by `decl_pi_inj` (§4.1, §4.2 stage 3) |
| R5 | (M1)'s binder cases need a renaming lemma first | the order (R), (U), (M1), (M2), (M3) (§4.2a) |
| R6 | case 2 needs `σ`'s objects to be M-free | the layer-correctness hypothesis; (M2) for M-free raw syntax; case 9 covers `pdef`'s inlining |
| R7 | `σ` is universe-weakened under level binders | (S4u), `guwkn_gosubst`, in cases 1 and 7 |

The smaller points are applied too: the fibre is typed code in the local
context `Δ[ρ]`; `letbox`'s dependent motive is argued; §4.1 lists the
recursor's and the level binders; §4.5 counts `t_J`'s level binders; and
the formalization is cited as the `heather-coq` repository.

### 4.5 The formal `Id` rules against the model (2026-09-30)

The formalization gained `Id` in its milestone M11
(`heather-coq/docs/design/M11_DESIGN.md`). Each rule below is from `Declarative.v`;
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

  **Mechanized** in `heather-coq/probes/NoUipJ.v`, closed under the
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
    global binders, six local ones and two level binders
    (`br_ar 24 = (2, 7, 6)`), the same pattern as the other branches. Its
    level binders are case 7's (S4u).

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
`heather-coq/theories/Validity/Uip.v`, since its M12). Before it had
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
(`heather-coq/theories/Validity/Hedberg.v`, closed under the global
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
| DeLaM globals, `□`, code recursors, `CΠ`/`TΠ`, δ | **argued by stratification (§4), independently reviewed (§4.4a)**; the layer facts it uses are side conditions of the Coq rules (§4.1); the semantic global substitution lemma is written out (§4.2a), its syntactic half on Coq-checked lemmas; the `□` fibres' invariance and `unf`'s idempotence **mechanized** (`BoxFibre.v`, `unf_idem`) |

The mechanization states contexts as reflexive graphs (morphisms and
identities only) and fibres as groupoid data. None of the groupoid laws is
used, so the results hold for groupoids in particular. Strict propositions
are Coq's `SProp`, whose definitional irrelevance is exactly the strict
uniqueness the model provides. Sections of a strict family are then an
`SProp`, and their irrelevance is checked by conversion alone.

What would strengthen it:
- A second pass over §4 as revised (§4.4a). Its weakest point is now
  (M3), representative independence, whose fibre case is mechanized and
  whose other three cases are argued. The lemma's semantic half is where
  any remaining slack is: (M1) is taken as standard, and the partial
  interpretation's full clause list is only summarized in §2 and §4.2a.
  The layer-D type globals, flagged here before the self-review, needed
  the independent review's R2: they never occur in code, but they occur
  in the contexts and types of code (§4.1), so they range over classes,
  a countable set.

## Appendix: Review of `docs/kernel/no-uip-model.md` §4 (2026-10-16)

Status: **independent paper review**, the one `docs/kernel/no-uip-model.md` §6
and `docs/kernel/iwf-former-design.md` §12.3 say is owed. **Resolved
2026-10-17**: every finding (R1–R7) and every smaller point is applied to
`docs/kernel/no-uip-model.md` §4 (its §4.4a maps each one to where it is fixed),
and the two pieces suggested for mechanizing at the end are checked in
Coq (`heather-coq`: `Typing/BoxFibre.v` and `unf_idem` in
`Syntax/Unfold.v`). The findings below are kept as written. It covers §4.1–§4.3
(the staged interpretation of globals and `□`) and §4.2a (the semantic
global substitution lemma). §4.5 is mechanized and was only read for
consistency. Nothing here is mechanized. Every rule and lemma cited is
from the Coq formalization (`heather-coq`, the doc's `../Lean/delam/`, at
`16ed0d5`), and each was checked to exist and to say what is claimed.

### Verdict

The outline holds. Interpreting `□` as a discrete set of code, in stages
over environments that carry syntax, is the right construction, and the
lemma's syntactic half rests on real Coq lemmas, all cited correctly.
Nothing found makes `UIP₀` derivable or touches §5's counterexample,
which lives in the global-free fragment.

But the interpretation as written does **not** validate three rules of
the formalization, each with a concrete instance (R1–R3 below). Each has
a local fix, and the fixes fit together. Four more steps are asserted
where an argument is needed (R4–R7). With the fixes, §4 becomes
correct as far as I can check it on paper. Its weakest point is then a
new semantic lemma, representative independence (R2), which the
document needs and does not state.

| | finding | severity | fix | status |
|---|---|---|---|---|
| R1 | level variables inside code: `box` ignores the level assignment, so `eqtm_ubeta` fails | breaks a rule | evaluate levels in box values; level-closed environments | resolved 2026-10-17 |
| R2 | context globals are raw syntax, but `eqtm_capp` and four other congruences relate D-convertible contexts and types | breaks a rule | products over D-conversion classes, plus a representative-independence lemma | resolved 2026-10-17 |
| R3 | definitions inside code: the recursion has no clause for a boxed `gdef`, which §4.3's scope admits | breaks totality | normalize box values with `unf` (M9's unfolding) | resolved 2026-10-17 |
| R4 | the recursor's branches bind layer-D and layer-V globals whose values come from the index type, not the code | gap | read the index up to D-conversion (`decl_pi_inj`); add V globals to environments | resolved 2026-10-17 |
| R5 | (M1) is not "two new clauses": its global and level binder cases need a renaming lemma first | gap, and an order | prove the global renaming instance first | resolved 2026-10-17 |
| R6 | the lemma is stated for every `σ`, but case 2 needs `σ`'s objects to be layer-correct | gap | add the hypothesis | resolved 2026-10-17 |
| R7 | `σ` is universe-weakened under `UΠ`/`Λ` and the recursor's level binders; §4.2a says levels are untouched | gap | cite `guwkn_gosubst` (S4u) | resolved 2026-10-17 |

R1–R3 are the ones to fix before the claim is restated. R4–R7 are
missing text, not wrong mathematics.

---

### R1. Level variables inside code

**What the document says.** §4.2a: an environment is "a level assignment
together with a closing substitution `ρ̂`", whose objects have "levels
read through the assignment". The clause table interprets `boxT T` as
"the code `T⦃ρ̂⦄` modulo level equivalence". So box values keep their
level variables. Case 1 says "Levels are untouched by `σ`."

**Why it fails.** Box contents can mention bound level variables.
`wf_ulam` types its body under `gctx_uwk n G`, and `wf_boxT`'s code is
typed under that `G`, so `Λℓ. box(Ty ℓ)` is well typed. Universe
substitution enters code (`usubst_ty`'s `boxT T => boxT (usubst_ty T φ)`,
`Term.v`). So `eqtm_ubeta` gives

```
(Λℓ. box(Ty ℓ)) $ [0]  ≡  box(Ty 0)      : □(· ⊢ @ 1)
```

The model gives the left side, at the extended assignment `ℓ ↦ 0`, the
code `Ty ℓ`, and the right side the code `Ty 0`. `lequiv` is equality
under *every* valuation (`Level.v`: `forall v, leval v l = leval v l'`),
so `ℓ ≢ₗ 0`. These are two different points of a discrete set, and the
rule fails.

**Fix.** Make box values closed in levels as well as in globals.
- An environment is `ρ = (v, ρ̂)`, with `v` a valuation of the level
  variables and `ρ̂`'s objects closed in levels: every level variable is
  replaced by the numeral `v` gives it. Write `⌜v⌝` for that level
  substitution.
- `⟦boxT T⟧ρ := T⦃ρ̂⦄[⌜v⌝]ᵤ`. On closed levels `≡ₗ` is equality of
  values, so "modulo level equivalence" is unchanged in meaning.
- `ρ·σ := (v, i ↦ (gosubst (σ i) ρ̂)[⌜v⌝]ᵤ)`. Case 5 then needs
  `usubst_gsubst` (`Universe.v`: `t⦃σ⦄[φ]ᵤ = t[φ]ᵤ⦃gousubst ∘ σ⦄`) next to
  (S1).
- Under `Λ`, `ρ̂` is level-closed, so it does not need weakening, and only
  `v` is extended.
- `letbox`'s β (§4.2a "What it validates") then compares `(ρ, ⟦box c⟧ρ) =
  (ρ, c⦃ρ̂⦄[⌜v⌝]ᵤ)` with `ρ·gsingle c`, which now has the same last entry.
  As written, the two differ by exactly this evaluation.

**New obligation.** `uapp`/`ulam` β and η are not consequences of §4.2a.
They need a *semantic universe substitution lemma*,
`⟦t[φ]ᵤ⟧(v, ρ̂) = ⟦t⟧(⟦φ⟧v, ρ̂)`. It is the same shape as §4.2a. Its box
case is `leval_lvsubst` (`Level.v`), and its global case is
`usubst_gsubst`. §2 lists `ΠΠ` as routine, which it is everywhere except
where code mentions a bound level. That case should be listed under
"What it validates", or as an obligation next to §4.2a.

---

### R2. Context and type globals are syntax, but conversion relates them

**What the document says.** Stage 2 assigns "a closed syntactic context
to each context global". The clause table interprets `clam t` as
`Δ₀ ↦ ⟦t⟧(ρ, Δ₀)` and says `CΠ` is a product "over context globals",
which read as raw contexts. `TΠ` is a product "over D-types up to
conversion". Representative independence is claimed only for `s_ρ` of a
layer-D type global, by stage-1 soundness.

**Why it fails.** Several M-rules relate D-*convertible* contexts and
types:
- `eqtm_capp` (`Declarative.v`): `capp t Δ ≅ capp t' Δ'` from
  `[G ⊢[lD] Δ ≅ Δ']`;
- `eqtm_tapp`: `tapp t A ≅ tapp t' A'` from `A ≅ A'` at D;
- `eqty_CTyp` and `eqty_CTrm`: `□(Δ ⊢ T) ≅ □(Δ' ⊢ T')` from D-conversion
  of both;
- `eqtm_elimT`/`eqtm_elimt`, `eqtm_tlam`, `eqty_tpi`, whose annotations
  `Δ`, `T` are compared at D.

A concrete failure: take `f : CΠ g. □(g ⊢ @0)` in `Γ`, `Δ := (x : Nat)`
and `Δ' := (x : El 0 ⌜Nat⌝)`. Then `Δ ≅ Δ'` at D, so
`capp f Δ ≡ capp f Δ'`. If `CΠ` is a product over raw contexts, `f` can
denote a family with `f(Δ) = box Nat` and `f(Δ') = box (El 0 ⌜Nat⌝)`.
That is a section the model must admit, and it refutes the rule.

**Fix.** Take both products over **classes**: `CΠ` over closed
D-contexts up to `[⊢[lD] Δ ≅ Δ']`, and `TΠ` over closed D-types up to D
conversion, as `TΠ` already says. Environments store a representative.
This is only well defined with a lemma the document does not state:

> **(M3) Representative independence.** If `ρ` and `ρ'` agree on V- and
> C-globals and on levels, and their context and layer-D type entries
> are pairwise D-convertible, then `⟦t⟧ρ ≃ ⟦t⟧ρ'` for every `t`, and the
> two interpretations of a context or type are the same family.

*Proof sketch*, by induction on `t`. A representative is read in four
places, and each is invariant:
1. **Through `s_ρ`**, by stage-1 soundness of D-conversion, as the
   document says. For contexts it is soundness of context conversion.
2. **Through a `□` fibre.** The set `{c | Δ₀ ⊢_C c : T₀}` is invariant
   under D-conversion of `Δ₀` and `T₀`. The reason is that a C-judgment's
   types live at `typeof lC = lD` (`Context.v`), so `wf_conv` at C
   converts at D, and context conversion (`CtxConv.v`) does the rest.
   §4.1's remark that "a layer-D global never occurs in code" is true but
   not enough: D-globals do occur in the *types and contexts* of code
   (`wf_boxt` checks `Δ` and `T` at `lD`), so the fibres depend on them.
3. **Through box values.** They do not read the representatives at all.
   `static_gsubst` (`GStatic.v`) is the syntactic form of this: C-code
   under substitutions that agree on static bindings is `≡ₗ`-equal, and
   neither `gdCtx` nor a layer-D binding is static.
4. **Through the recursor's context and index.** By induction on the code,
   with R4's reading of the index.

Once (M3) holds, the products over classes are well defined, `eqtm_capp`
and its siblings hold, and the `TΠ` remark in §4.2 stage 3 ("ranges over
syntax, a countable set") stays true of the classes.

---

### R3. Definitions inside code

**What the document says.** §4.3 puts "a global context of definitions
only" in scope. §4.2a's environment maps each definition to itself, and
case 9 interprets `gdef j b d` through its inline body. Stage 3 says that
"code recursors recurse on the syntax `t(γ)` … with β by definition".

**Why it fails.** A definition can occur in code: `wf_gdef` needs only
`lle lC i`, and there is no δ at C (`eqtm_delta` requires `compt i`). So
`box(gdef u b d)` is a closed code, and the recursor has no branch for it.
`redt`'s `| _ => None` (`Recursor.v`) leaves it stuck, as M9 intends
(`whne_elimt_gdef`; the witness `stuck_rec_wf` in `Validity/DefStuck.v`).
The model's □ fibre contains that code, and the semantic recursion must
return a value of the motive *at that code*. Recursing on the unfolding
`b[d]` gives a value at a different point of `□`, so it is in the wrong
fibre. As written, the recursion is partial on a fibre the scope admits.

**Fix.** Normalize box values by M9's unfolding:
`⟦box t⟧ρ := unf(t⦃ρ̂⦄)[⌜v⌝]ᵤ`, with environment entries stored in the
same normal form. Then `box(gdef u b d)` and `box(b[d])` denote the same
point. The model identifies more code than C-conversion, which is sound,
and the recursion never meets a `gdef`. What it costs:
- `unf` commutes with global, universe and local substitution:
  `unf_gsubst`, `unf_usubst`, `unf_subst` (`Syntax/Unfold.v`, all
  checked). So case 5 and (S4) survive.
- Interpretations are invariant under unfolding an environment entry,
  since stage 1 already reads `gdef` through its body. It is one more
  clause of (M3).
- Normal forms need idempotence, `unf (unf t) = unf t`. It is not in Coq
  as stated, but `unf_gfree` plus "`unf` is the identity on definition-free
  syntax" is a short induction.

The recursor β is unaffected. When the scrutinee's head is a former,
`redt`'s reduct passes the unnormalized sub-code to the branch, and the
model passes its normal form; by the invariance just stated they agree.
The model then computes `elim(box(u^δ))`, which the syntax leaves stuck.
That is consistent with M9's `stuck_rec_not_numeral`, since the model may
identify more than the syntax.

The alternative is to drop definitions from §4.3's scope. `unfolding`
(`Typing/Unfold.v`) does not by itself make that free: it gives
derivability of the unfolded judgment in `unf_G G`, not a derivation free
of `gdef`, so the model still has to interpret intermediate
`box(gdef …)` terms. The normalization fix is simpler.

---

### R4. The recursor binds globals the environment does not cover

§4.1 lists the global binders as `letbox` (layer C), `TΠ` (layer D) and
`CΠ` (contexts). The recursors' branches also bind globals, and two kinds
are new (`brDecls`, `Typing/RecSpec.v`):
- **branch 4, `t_x`**: `U_T : (g ⊢ @ℓ)` at **layer D**, and
  `u_x : (g ⊢ U_T @ℓ)` at **layer V**;
- **branch 11, `t_λ`**: `U_T : (g, x : U_S ⊢ @ℓ')` at **layer D**.

There are two consequences:
- **Environments need layer-V term globals.** Their value is a code
  (here, a variable), treated like a C-global. (M2) must cover V. Stage 2
  lists only C, D and context globals.
- **The λ case reads the index, not the code.** `lam` stores no codomain,
  so `redt` takes it from the index `T`, and only when `T` is
  syntactically a `Π` (`match T with tyPi _ _ _ B => … | _ => None`,
  `Recursor.v`). The model cannot copy that. The index may be D-convertible
  to a `Π` without being one: `El (tmPi …)`, or a D-global whose
  representative is not a `Π`. (M3) also forbids reading its syntax. So
  the model's λ case takes `U_T` to be the class of `B`, where
  `T ≅ Π A B` at D:
  - such a `B` exists by inversion of the C-typed `lam` and `wf_conv`;
  - it is unique up to D-conversion by `decl_pi_inj`
    (`Validity/DeclConsequencesP.v`).

  The model therefore computes where the syntax is stuck, which is sound.

Stage 3 should say that the recursion is defined on *typed* code. Each
step reads a typed sub-code by C-inversion, at the context and index
that `redT`/`redt` give it. The reducts' typing (`rec_red_typed`,
`Validity/RecReduct.v`, which types the pieces by inverting the code's
C-typing) is what keeps the recursion inside the fibres. The recursion is total on typed,
global-closed, definition-free C-code: each head is one of the 61
branches. I checked this against the `tm`/`ty` constructors.

---

### R5. (M1) is longer than stated, and it comes second

§4.2a: "(M1) … The two new clauses are immediate: the global-variable
case … and the box case." Local substitution goes under every global and
level binder (`subst_tm`, `Term.v`):
- `letboxT`/`letboxt` and `bindG`: `t'[gwk d]`;
- `clam`/`tlam`: under `gwk d`;
- `ulam` and `bindU`: under `uwk d` (resp. `uwkn n d`);
- `bindL`: under `llift d`.

So (M1)'s `letbox`, recursor, `CΠ`/`TΠ` and `UΠ` cases need
`⟦gwk d⟧(ρ, c) = ⟦d⟧ρ`, which is the semantic lemma at `σ := ↑`.
§4.2a derives that from the main lemma, whose case 2 uses (M1). The
circle is only apparent, but the order has to be stated:
1. **(R) the renaming instance** `⟦t⦃ξ⦄⟧ρ = ⟦t⟧(ρ∘ξ)`, for global
   renamings. All its objects are `GId`s, so only cases 3, 4 and 9 occur
   and (M1) is never used. Its binder cases are (S4) for renamings.
2. A **universe renaming** analogue for `uwk d`, by the same induction.
   Under R1's level-closed environments it is the observation that a
   level-closed object is fixed by universe renaming.
3. **(M1)**, using (R) and step 2 at the binders.
4. **(M2)**, then the main lemma.

---

### R6. The lemma's hypotheses

§4.2a states the lemma "for every raw … `t`, every `σ : Ψ ⇒ Ψ₀` and
every `ρ`". Case 2 applies (M2) to `σ`'s object `c` "which is
well-typed at layer C". For a raw `σ` nothing makes `c` free of M
constructs. Stage 1 is undefined on `box` or `letbox`, while the left
side `⟦c[d⦃σ⦄]⟧ρ` is the stage-3 interpretation of `c`, which may be
defined. Then the Kleene equality fails.

**Fix.** Assume `σ` is layer-correct: each object for a V-, C- or
D-global is free of layer-M syntax, and each is of the binding's sort.
Assume the same of `ρ̂`. A well-typed `σ` satisfies this by inversion,
since a judgment at a layer below M uses no M rule. State (M2) for
M-free raw syntax, not "a term at layer C or D", and the lemma becomes
one about raw `t` under such `σ` and `ρ`. Case 9 needs no hypothesis.
Since M9's follow-up, `pdef` inlines the body when `σ` sends a definition
to a non-variable. Then `(gdef i b d)⦃σ⦄ = b⦃σ⦄[d⦃σ⦄]`, and (M1) with the
induction hypothesis on `b` and `d` closes it. "A well-formed `σ` sends
`i` to a defined `GId j`" is one of two cases, not a restriction.

---

### R7. `σ` under level binders

Case 1 lists `ΠΠ`/`Λ`/`$` as compositional, with "Levels are untouched
by `σ`". But `gsubst_ty (tyUPi n l T) σ = tyUPi n l (T⦃guwkn n σ⦄)`, and
likewise for `ulam`. The recursor bundle's `bindU` substitutes under
`guwk σ`, and branch `k` is instantiated through
`gbsub k σ = gupn (br_ng k) (guwkn (br_nu k) σ)` (`RecGSubst.v`). Case
7's "`b⦃gupⁿ σ⦄`" is missing the universe weakening.

The needed fact is the level-binder analogue of (S4), and it is checked:
`guwkn_gosubst` (`GSubst.v`) gives `guwkn k θ = gosubst (guwkn k σ ·)
(guwkn k τ)` when `θ = gosubst (σ ·) τ`. Add it as **(S4u)**. Use it
together with (S4) in cases 1 (`UΠ`, `Λ`) and 7 (the branches' level
binders and the motives, which are substituted too). Under R1's
level-closed environments the semantic side is simpler, since `guwk ρ̂ = ρ̂`.

---

### Smaller points

- **§4.2 stage 3, `□`'s fibre.** It is closed code "of type `T[ρ]`",
  which should say *in the local context `Δ[ρ]`*: code is global-closed,
  not local-closed. Also say it is a set of *well-typed* syntax, so the
  interpretation reads the typing judgment of the empty global context.
  That is harmless, since it is a set, and it is what makes R4's
  inversions available.
- **`letbox`'s dependent motive.** `wf_letboxT` types the body at
  `M⟪S⟫[box(u^id)]`. That `⟦t'⟧(ρ, t(γ))(γ)` lands in `⟦M[t]⟧ρ(γ)` uses
  three facts:
  - (R) on `M`;
  - `⟦box(u^id)⟧(ρ, c) = c`, from `gvar 0 (lshift 0)` and `(S3)` at the
    identity substitution;
  - (M1).

  Naturality uses the morphism `(α, id_c)` of `Γ.□`. This is all
  routine, but stage 3 only argues the object part.
- **§4.1's binder list.** Add the recursor's binders (R4) and level
  binders (`UΠ`, `Λ`, `bindU`). The sentence "box contents are layer-C
  code" is right. The box's *context and type* are checked at D
  (`wf_boxT`, `wf_boxt`, `wft_CTrm`), which is what R2 needs.
- **§4.5, case 7.** "Seven global binders and six local ones" for `t_J`:
  `br_ar 24 = (2, 7, 6)`, so there are also two level binders (R7).
- **Paths.** The document cites the formalization as `../Lean/delam/…`.
  In this project it is the `heather-coq` repository. A reader outside
  the original checkout cannot follow the links.

### What checks out

- **The §4.1 layer facts.** Each is a side condition of the cited rule,
  as claimed: `wft_gvar`/`wf_gvar` (`lle i' i`), the M-only rules for
  `□`, `letbox`, the recursors, `CΠ`, `TΠ` and `UΠ`, and `letbox` binding
  at `lC` (`gdTy Δ lC l`, `gdTm Δ lC T l`). Static Code is two-sided:
  `static_code` (`StaticCode.v`), and `static_code_eqty`,
  `static_code_eqtm` and `static_code_eqctx` (`StaticCodeEq.v`).
- **(S1)–(S5).** They are as stated: `gsubst_gsubst_all`,
  `gsubst_subst_all`, `gsubst_gren_all`, the `ptm`/`pty`/`pctx`/`pdef`
  clauses, and `subst_gvar` (`Commute.v`). For (S4), `gup σ (i+1) =
  goren (σ i) S`, and `(ρ̂, c)` composed with `S` is `ρ̂`. For
  `ρ·gsingle c = (ρ, c⦃ρ̂⦄)`, `gsingle o` is `(o, id)` (`Term.v`).
- **Cases 2, 3, 5 and 6** are right once R1, R3 and R6 are in place.
  Case 8 is right once R2 is.
- **Size.** `□` lives at `lzero` (`wft_CTyp`, `wft_CTrm`) and denotes a
  countable discrete set, so it is κ₀-small. `CΠ` (at `l`) and `TΠ` (at
  `l'`) are products over countably many classes of κ_l-small groupoids,
  and so stay κ_l-small for inaccessible κ_l. No universe has a code for
  `□`, `CΠ` or `TΠ`. `UΠ` sits at `ω` and is not classified.
- **`letbox`'s naturality.** It holds as argued: a section of a discrete
  family is constant on connected components.

### Suggested order of revision

1. Rewrite the environment as `(v, ρ̂)` with level-closed, unfolded
   entries (R1, R3), and products over classes (R2). Update the clause
   table.
2. State (M3) with its proof sketch, and (S4u).
3. Add V-globals and the λ index reading (R4).
4. Restate the lemma with R6's hypothesis, and give the R5 order.
5. Add `uapp`/`ulam` β/η and the recursor congruences to "What it
   validates".

The pieces most worth mechanizing next, if anyone does, are the □
fibre's invariance under D-conversion (R2 item 2), which is a typing
lemma close to what Coq already has, and `unf`'s idempotence (R3).

**Done (2026-10-17).** Both are mechanized in `heather-coq`, with no
admits or axioms:
- `box_fibre_ty_iff` and `box_fibre_tm_iff` (`Typing/BoxFibre.v`), along
  `eqty_CTyp`'s and `eqty_CTrm`'s premises, as corollaries of
  `ctxconv_ty`/`ctxconv_tm` with `wf_conv` and `wf_lconv`;
- `unf_idem`, `unf_idem_ty`, `unf_idem_ctx`, `unf_l_idem` and
  `unf_o_idem` (`Syntax/Unfold.v`), directly by one mutual induction: the
  `gdef` case is `unf_subst` and the induction hypothesis on the body, so
  the route through `unf_gfree` was not needed.
