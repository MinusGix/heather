# The `Wf` former: finitary branching inductives in the kernel

Status: **phases 1–4 landed** (2026-07-25); §9 tracks the remaining round.
Written as a design sketch before the code, per repo discipline, and kept as
the specification the implementation is checked against. This is the
route-C landing from `docs/branching-inductives-choice.md` §6/§12. Decision
evidence:
`branching-inductives-choice.md` §15 and the three prototype files

- `crates/elab/tests/branching_route_a.rs` (what W + funext costs, measured),
- `crates/elab/tests/branching_route_c.rs` (the per-constructor interface),
- `crates/elab/tests/branching_route_c_nary.rs` (the generic n-ary
  interface, the Fin-ih, and the Σ-η bridging — all validated against the
  current kernel).

Tracking issue: `issues/wf-former.md`.

The design principle, stated once: **store children where the kernel's η
already reaches.** `W` stores children in `Π`, the one type family this
kernel deliberately does not η-expand, and that single fact is the source of
every funext obligation route A pays. `Wf` stores them in `Σ`/`Unit`, whose
η is in `conv.rs` today — the prototype demonstrated that
`supf (inr u) cs ≡ node (fst cs) (fst (snd cs))` for *neutral* `cs` is
already a theorem of the current checker. The former is not new definitional
power; it is a data representation aligned with the power we have.

---

## 1. New formers

Three, all small. `Vec` and `Fin` are index-computing wrappers over existing
formers; `Wf` is the fixed point.

### 1.1 `Vec` — fixed-length tuples

```
Γ ⊢ T : Type @ l        Γ ⊢ k : Nat
------------------------------------
Γ ⊢ Vec^l(T; k) : Type @ l

Vec^l(T; 0)    ⇝  Unit
Vec^l(T; S k)  ⇝  Σ^{l,l}(_ : T). Vec^l(T; k)
```

Type-level reduction on the (whnf'd) length; **neutral at a neutral
length**, no η of its own — η arrives through the reductions (`Unit`
proof irrelevance at 0, `Σ`-η at successors), which is the entire point.

This is the `vec` formula from the tier-1 fording round
(`tier1_fording.rs` §3) promoted from a derived `elim_Nat` code into a
former, which is what removes wrinkle 1 of the choice doc: the elements no
longer need to be *code-expressible*, so `Vec(Wf …; k)` is stateable with no
side condition on shapes.

*Level defect (found in the ch. 07 round, §8; **open**).* The nullary reduct
`Unit` does not carry `l`, so a well-formed `Π^{1,0}(_ : Vec^1(T;0)). Nat`
steps to an ill-formed one: type-level preservation fails for `l ≠ 0`. `Vec`
is the first former whose whnf is chosen by a term that does not carry a
level (`El`'s does), and this is the one place that shows. The successor
case preserves `l` exactly, and `Fin` needs nothing — declared at `0`, both
reducts land there. The one-line repair (level-polymorphic `Unit`) is wrong:
it gives `box Unit` a type at every level, which the code eliminator cannot
survive. Tracked with three costed candidates in
`issues/unit-level-and-vec-preservation.md`; it does not affect anything else
in this document.

### 1.2 `Fin` — canonical finite index types

```
Γ ⊢ k : Nat
----------------------
Γ ⊢ Fin(k) : Type @ 0

Fin(0)    ⇝  Empty
Fin(S k)  ⇝  Unit +^{0,0} Fin(k)
```

Same discipline: reduce on canonical length, neutral otherwise. Index
literals are `inl ⟨⟩`, `inr (inl ⟨⟩)`, … as in the prototype.

*Alternative considered:* `Fin` (unlike `Vec`) never mentions `Wf`, so it
could stay a derived `El (elim_Nat …)` schema inlined into the `elim_Wf`
rule — the n-ary prototype did exactly that and it works. The former is
chosen anyway: it is two trivial reductions, symmetric with `Vec`, its LR
case is a restriction of `Vec`'s, and it makes every generated ih goal read
`Π(i : Fin 2). …` instead of `Π(i : El (elim_Nat …)). …`. If the ch. 07
round wants to shed weight, this is the piece to shed — nothing else
depends on `Fin` being primitive.

### 1.3 `Wf` — the finitary branching fixed point

```
Γ ⊢ S : Type @ l        Γ, x : S ⊢ n : Nat
-------------------------------------------
Γ ⊢ Wf^l(x : S). n : Type @ l
```

Shapes `S` (one per constructor-with-payload, in generated use), arity `n` a
`Nat` *term* with the shape free. Contrast with `W`: the positions are a
number, not a type, so the type lives at `l` alone and the children are a
tuple, not a function.

---

## 2. Introduction

```
Γ ⊢ a : S        Γ ⊢ cs : Vec^l(Wf^l(x:S).n; n[a/x])
-----------------------------------------------------
Γ ⊢ sup_f^l(x:S. n; a; cs) : Wf^l(x:S). n
```

Fully annotated (shape, arity, level) so it synthesizes, like `Sup`. At a
neutral `a` the children type is a stuck `Vec` — checkable, uninhabitable
by literal tuples, which is the right behaviour (wrinkle 3: an unknown
shape has an unknown arity; generated code cases on the tag first).

---

## 3. `nth` — derived, not primitive

`nth` is a fixed `elim_Nat` schema, stateable without codes now that `Vec`
and `Fin` are formers. For any `T : Type @ l`:

```
nth^l(T; k; cs; i) :=
  elim_Nat^l( k̂. Π(cs : Vec(T; k̂)). Π(i : Fin k̂). T
            ; λ(cs : Unit). λ(i : Empty). elim_Empty(_. T; i)
            ; k̂ r. λ(cs : Σ(_:T). Vec(T; k̂)). λ(i : Unit + Fin k̂).
                     case i of { inl _ ⇒ fst cs | inr j ⇒ r (snd cs) j }
            ; k) cs i
```

Validated behaviour (n-ary prototype, `nth_computes_to_the_projections`):
at a literal `k` and a *neutral* tuple, `nth` reduces to the projections —
`nth(T; 2; cs; i₀) ≡ fst cs` — which is what makes the n-ary ih usable.
The kernel's `elim_Wf` typing and β rules **materialize this schema**; that
is a rule containing a constructed term, with precedent in `elim_W`'s β
synthesizing the ih λ (`crates/kernel/DESIGN.md`, W section).

---

## 4. Elimination and β

```
Γ ⊢ t : Wf^l(x:S).n        Γ, z : Wf ⊢ M : Type @ l'
Γ, a : S,
   cs : Vec^l(Wf; n[a/x]),
   ih : Π(i : Fin n[a/x]). M[nth(Wf; n[a/x]; cs; i)/z]
 ⊢ s : M[sup_f(a; cs)/z]
------------------------------------------------------
Γ ⊢ elim_Wf^{l,l'}(x:S.n; z.M; a cs ih. s; t) : M[t/z]
```

β, firing on the constructor whatever the label and children are (open
subterms included — the route-A property we keep):

```
elim_Wf(x:S.n; z.M; a cs ih. s; sup_f(_; a₀; cs₀))
  ⇝ s[ a₀, cs₀,
       λ(i : Fin n[a₀/x]). elim_Wf(x:S.n; z.M; a cs ih. s;
                                    nth(Wf; n[a₀/x]; cs₀; i)) ]
```

The recursive call is synthesized under a λ exactly as in `elim_W`'s β —
the same "only β rule that builds a binder" shape, now at a `Fin` domain.
The ih's η-deficiency as a function is harmless because the ih is
*transient*: applied at (literal, after tag-casing) indices, never stored
in data, never compared — this was wrinkle 6.2, resolved by the n-ary
prototype. No dependent-vector former, no mutual forest presentation.

Why the arm obligation needs no bridging (the funext-shaped gap of route
A): in the generated recursor the step cases on the tag first, so within
each branch `n[a/x]` is a literal, `Vec` reduces to a Σ-chain, and the
user-arm's constructor form `sup_f(tag; (c₁, (c₂, ⟨⟩)))` is convertible
with `sup_f(tag; cs)` for the *abstract* `cs` by Σ-η + Unit-η — pinned by
`sigma_eta_bridges_the_constructor_form` against today's `conv.rs`.

---

## 5. Conversion and neutrality

- `Wf` is **positive, no η** — like `Sum` and `W`. Type conversion at
  `Type::Wf` is structural: shapes convertible, arities convertible (one
  binder), levels equal.
- `sup_f` values compare by label and children; the children comparison
  happens at `Vec` type, where the reductions hand it to `Σ`-η /
  `Unit`-irrelevance componentwise. Canonical-form uniqueness for generated
  data follows with **no new conversion code at `Wf` itself**.
- `elim_Wf` is neutral on a neutral scrutinee.
- `Vec`/`Fin` are neutral at neutral length; two neutral `Vec` types
  compare by element type and length.

The `conv.rs` footprint is: two type-reduction cases (`Vec`, `Fin`), one
structural type-compare case each (`Vec`, `Fin`, `Wf`), one neutral-elim
case (`elim_Wf`). No change to the Π arm, no change to the existing η
rules — the "ch. 06 verbatim" discipline stays intact where it matters.

---

## 6. Codes and the meta layer

New code formers, with `El` computing as usual (`TmId` is precedent for
codes containing terms; `TmSigma`'s `snd` is precedent for codes binding a
term variable):

```
TmVec { level, elem: code, len: term }         El(TmVec t k)   ⇝ Vec(El t; k)
TmFin { len: term }                            El(TmFin k)     ⇝ Fin(k)
TmWf  { level, shape: code, arity: term ⟨x⟩ }  El(TmWf s x.n)  ⇝ Wf(El s; n')   (n' over El s)
TmSupf, TmElimWf                               — term formers, mirroring §2/§4
```

*Implementation note (phase 3, landed):* the last line needed no new enum
variants — `sup_f`/`elim_Wf` are ordinary terms that become code once the
layer gate lifts, exactly as `sup`/`elim_W` are; only their **branches**
`tm_supf`/`tm_elim_wf` are new. Note also that `ty_vec`/`ty_fin`/`ty_wf`
are type-motive branches whose length/arity recursive call sits at the
*term* motive (`ty_el`'s shape), and that they bind one universe or none,
not `W`'s two: an arity is a term and carries no level.

Code-recursor bill (`crates/kernel/src/rec.rs`), using the W landing as the
yardstick (4 branches, 37 total, `tm_elim_w` deepest at 3 univs / 6
globals / 5 recursive calls): `ty_vec`/`tm_vec`, `ty_fin`/`tm_fin`,
`ty_wf`/`tm_wf`, `tm_supf`, `tm_elim_wf` — **8 branches, 37 → 45**, with
`tm_elim_wf`'s telescope comparable to `tm_elim_w`'s. The same five
parallel transcriptions apply (rec.rs, subst depths, reduce β,
`BRANCH_DIMS`, `identity_branches` ×2, `gen_branches`). This is the
expensive part and the reason the former set was kept minimal; dropping
`Fin` (§1.2 alternative) saves 2 branches if the round runs heavy.

---

## 7. The generator (one regime)

A surface declaration `inductive D { C₁(p̄₁, r₁ rec fields), … }` lowers to:

- **Shape** `S` = the tier-0 sum-of-payload-records with the nominal-tag
  discipline unchanged (`docs/inductive-tier0-lowering.md` §3.3).
- **Arity** `n` = case on the tag, returning each constructor's literal
  recursive-field count.
- **Constructors** = `sup_f` with literal `Vec` tuples (recursive fields in
  declaration order).
- **`match`/recursor** = `elim_Wf`, stepping by the commuted case over the
  tag with `cs`/`ih` generalized in the case motive — the discipline all
  three prototypes use; within each branch the arity is literal, so `Vec`
  and `Fin` reduce and the user-facing arms have tuple children and
  per-child ihs (`ih i₀`, `ih i₁`, …).
- **No-confusion** = tag predicates by large elimination on `S` (tier-0
  §6 style); injectivity by `nth` projections. The height machinery of the
  fording scheme is not used.

Scope of the one regime:

- **Tier 0 and the linear tier fold in.** `List`/`Bits`-style types become
  arity-≤1 `Wf` declarations; the exact-height fording scheme retires from
  the generator. `tier1_fording.rs` stays as a kernel stress suite, and its
  `vec` formula survives as the `Vec` former's reduction semantics.
- **`Rose`-style nesting is nearly free**: `Rose { Node(A, List Rose) }` is
  `Wf` with `S = Σ(a : A). Nat` and `n = snd x` — the list of children *is*
  the `Vec`, its length is data in the shape. This was §14's unscored point
  in the choice doc; it falls out of arity-as-a-term.
- **Unchanged**: indexed families still ford by `Id` (tracked separately);
  `W` + funext remain the infinitary tier (`Acc`) — `Acc`'s positions are a
  type, not a `Nat`, and that tier never computed anyway. Two branching
  formers in the kernel, serving genuinely different quantification shapes.

---

## 8. Metatheory (ch. 07) obligation — **done**, and passed

Landed 2026-07-25 as part II of `docs/metatheory-ch07-extensions.md`
(§§10–17). **The abort criterion was not triggered; the decision stands.**
Results, against what this section predicted:

- **`Vec`/`Fin` cost *no* LR case**, which is stronger than the prediction
  above. Every type-relation rule is keyed on the whnf; at a canonical
  length these formers reduce away and the `Unit`/`Σ`/`Empty`/`+` rules
  apply through weak-head expansion, and at a neutral length they *are* the
  whnf and the existing neutral-type rule applies. They owe two
  Congruence-for-Neutrals laws, and those are a new *kind* — the first
  neutral-type congruence with a type premise (`El ν`'s premise is a term).
- **`Wf` is a restriction of `W`'s in three senses.** Its type rule is
  `W`'s with a term relation at `Nat` in place of the position-type
  relation; its term relation replaces `W`'s subtree quantifier with a
  finite Σ-spine, recursing on the arity's `NfEqNat` derivation (*not* on
  either length — the two sides' arities are related, not equal); and its
  layering-restriction case has one contravariant premise where `W` has two.
  `NfEqWf` is a `Wf`-shaped inductive definition where `NfEqW` is a
  `W`-shaped one, so the *metatheory's* induction requirement drops too.
- **The one new obligation** is the index lemma: `elim_Wf`'s arm needs
  relatedness at arbitrary `Fin` indices, which the finite spine does not
  hand over directly. Four cases, all reductions the kernel already
  performs. That is the entire price of finitarity.
- **No funext obligation appears in the `elim_Wf` arm.** The only `Π` is the
  ih, and the `Π` term relation is the applied form — the semantic
  counterpart of "the ih is transient" (§4).

**One real defect fell out**: `Vec^l(T;0) ⇝ Unit` drops the level, breaking
ch. 06's *Preservation* lemma for `l ≠ 0`. It survived since phase 1 not
because the witness was rare — the generator produces it routinely — but
because the property that would observe it did not exist: the suite had the
*term* half of preservation and no type half. That property now exists and
fails on seed 102. The defect itself is **open**: the one-line repair breaks
uniqueness of types at `□`, and the code eliminator depends on that. See
§1.1, `docs/metatheory-ch07-extensions.md` §10.3, and
`issues/unit-level-and-vec-preservation.md`.

---

## 9. Sequencing and acceptance

1. ~~**This document reviewed** and the rule set frozen.~~ Done.
2. ~~**`Vec` + `Fin` land first**~~ Done (`crates/kernel/tests/vec_fin.rs`). — self-contained, two reductions each,
   their own conversion tests. Nothing about them is speculative.
3. ~~**`Wf`/`sup_f`/`elim_Wf`**~~ Done (`crates/kernel/tests/wf.rs`), with
   the conversion tests the postulate prototypes could not run: β on open
   subterms, canonical-form uniqueness, neutral behaviour, and the
   nth-schema materialization in typing and β.
4. ~~**Acceptance**~~ Met, in `crates/kernel/tests/wf.rs`: `Tree` is built
   on the real former and `mirror (mirror t) = t` goes through with every
   β-marker deleted — the Leaf arm is literally `refl_tree(leaf())`, the
   Node arm is cong + cong + trans, and the constructor-form gap that route
   A bridges with funext is closed by conversion so it never appears in the
   proof. `branching_route_a.rs` is kept unchanged as the record of what was
   not chosen. Two implementation notes worth carrying to phase 3: the
   motive is an ordinary `Type` binding `z` (no `Ty`-code round trip, unlike
   the postulate prototypes, because the eliminator is a former), and
   `Empty`-η turned out **not** to be needed for the Leaf arm — arity 0 is
   `Vec(T;0) ⇝ Unit`, whose proof irrelevance already collapses every
   nullary constructor form.
5. ~~**rec.rs round** (§6)~~ Done (`crates/kernel/tests/wf_codes.rs`), 45
   branches, layer-c gate removed.
6. ~~**ch. 07 round** (§8)~~ Done — `docs/metatheory-ch07-extensions.md`
   part II. Abort criterion **not** triggered; one kernel defect found and
   fixed (§1.1).
7. **Generator round** (§7) — at which point
   `issues/tier1-branching-constructors.md` closes.
