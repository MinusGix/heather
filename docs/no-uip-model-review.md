# Review of `docs/no-uip-model.md` §4 (2026-10-16)

Status: **independent paper review**, the one `docs/no-uip-model.md` §6
and `docs/iwf-former-design.md` §12.3 say is owed. **Resolved
2026-10-17**: every finding (R1–R7) and every smaller point is applied to
`docs/no-uip-model.md` §4 (its §4.4a maps each one to where it is fixed),
and the two pieces suggested for mechanizing at the end are checked in
Coq (`heather-coq`: `Typing/BoxFibre.v` and `unf_idem` in
`Syntax/Unfold.v`). The findings below are kept as written. It covers §4.1–§4.3
(the staged interpretation of globals and `□`) and §4.2a (the semantic
global substitution lemma). §4.5 is mechanized and was only read for
consistency. Nothing here is mechanized. Every rule and lemma cited is
from the Coq formalization (`heather-coq`, the doc's `../Lean/delam/`, at
`16ed0d5`), and each was checked to exist and to say what is claimed.

## Verdict

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

## R1. Level variables inside code

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

## R2. Context and type globals are syntax, but conversion relates them

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

## R3. Definitions inside code

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

## R4. The recursor binds globals the environment does not cover

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

## R5. (M1) is longer than stated, and it comes second

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

## R6. The lemma's hypotheses

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

## R7. `σ` under level binders

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

## Smaller points

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

## What checks out

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

## Suggested order of revision

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
