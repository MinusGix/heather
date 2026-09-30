# UIP is not derivable without `transp`: a groupoid-model argument

Status: **paper argument, 2026-09-30**, not reviewed. §3 and the two
counterexamples of §3.4 and §5 are **mechanized**:
`../Lean/delam/probes/NoUipComponents.v`, closed under the global context.
§4 is argued only.
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
logical relation. The interpretation here uses only the property their
proof also relies on, the **layering restriction**: code (layer C)
contains no `□`, no code recursor and no layer-M construct, and a layer-D
judgment contains no `□` either (`Layer::Prog` is "vanilla MLTT with
computation", `crates/kernel/src/layer.rs`).

- **Global contexts.** A global variable `u : (Δ ⊢_i T @ l)` stands for
  *syntax*: global substitutions replace it by a term. Interpret a
  global context `Ψ` by the **set** `Inst(Ψ)` of closed well-typed
  instantiations (for layer-D type globals, taken up to D-conversion).
  Interpret a judgment under `Ψ` as an `Inst(Ψ)`-indexed family of
  groupoid-model data. `Inst(Ψ)` is a set, so no naturality across
  instantiations is needed. Global weakening and substitution are
  reindexing along maps of sets, and are strict.
- **A global used in a term** (`u^δ`, or `U` in type position) at
  instantiation `ρ` is interpreted as `⟦ρ(u)⟧`. That is well-founded:
  `ρ(u)` is closed code, with no global variables. Closed code is
  interpreted first, as a layer-D derivation (code lifts to D,
  `Typing/Lifting.v` in the Coq formalization), before any
  instantiation-dependent judgment.
- **`□(Δ ⊢ Ty l)` and `□(Δ ⊢ T @ l)`**: the *discrete* groupoid of closed,
  well-typed code at that type, up to α. Conversion at `□` is syntactic,
  which matches (`conv.rs`: box conversion is syntactic). `box t` is
  `t`. `letbox` extends the instantiation.
- **Code recursors** (`ElimCodeTy`, `ElimCodeTm`): structural recursion
  on the syntax, with β by definition and one branch per code former
  (the per-former branches of `rec.rs`).
- **`CΠ`, `TΠ`** (meta-level abstraction over local contexts and layer-P
  types): products over the set of local contexts, and over layer-P types
  up to conversion. A layer-P global never appears inside code, by the
  layering restriction, so only its interpretation is used.
- **Bodied globals** (δ): interpreted by their bodies.

This is the least standard part. It is argued, not checked. The
constructions are set-indexed and never interact with the groupoid
structure of `Id`, which is all the UIP question needs.

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
| DeLaM globals, `□`, code recursors, `CΠ`/`TΠ`, δ | **argued by stratification (§4)**; no published model of DeLaM |

The mechanization states contexts as reflexive graphs (morphisms and
identities only) and fibres as groupoid data. None of the groupoid laws is
used, so the results hold for groupoids in particular. Strict propositions
are Coq's `SProp`, whose definitional irrelevance is exactly the strict
uniqueness the model provides. Sections of a strict family are then an
`SProp`, and their irrelevance is checked by conversion alone.

What would strengthen it:
- A review of §4 by whoever next touches DeLaM's metatheory: the
  instantiation sets for layer-D type globals (up to conversion) are
  where the argument has the least slack.
