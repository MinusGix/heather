# Level-indexed `Unit^l` / `Empty^l`: rules, and the routes not taken

**Decision: 2026-07-25, route (a).** Written before the code, in the house
pattern of `docs/wf-former-design.md` — this is the spec the implementation is
checked against, and §6 is the historical record of what was rejected.

Tracking issue: [[unit-level-and-vec-preservation]]. Companion decision record
for the surrounding round: `docs/branching-inductives-choice.md`.

---

## 1. The defect this closes

`Unit` and `Empty` are fixed at level 0 (`typing.rs:499`). `Vec^l(T; 0) ⇝ Unit`
therefore drops `l`, and DeLaM ch. 06's *Preservation* lemma (`06:264`) fails
for every `l ≠ 0`:

```
⊢ Π^{1,0}(_ : Vec^1(Ty 0; 0)). Nat @ 1        well-formed
  ⇝  Π^{1,0}(_ : Unit). Nat                   LevelMismatch
```

It is **not only a broken lemma.** Measured on the pre-fix kernel:

```
Vec^1(Ty 0;0) well-formed @1 : Ok
  ..its whnf                 : Unit
Triv : Vec^1(Ty 0;0) @ 1     : Err(LevelMismatch)
Triv : Vec^1(Ty 0;0) @ 0     : Ok
```

`Vec^l(child; 0)` is the children type of a **nullary constructor** of a `Wf`
whose shape sits at level `l` — i.e. any polymorphic branching inductive. So
today `Leaf` cannot be built for `Tree<A>` when `A : Type l`, `l > 0`. That is
a functional hole, and it is the reason this is worth a real round rather than
a patch.

Monomorphic inductives are unaffected: a tier-0/tier-1 shape is a sum of
records at level 0, so the nullary arm is `Vec^0(…; 0)` and everything works.
That is why this hid from phase 1 to phase 4 of [[wf-former]].

---

## 2. Rules

Parameterize rather than polymorphise: distinct types at distinct levels,
exactly as non-cumulative systems do it (Agda's `record ⊤ {ℓ} : Set ℓ`).
`Ty ℓ` is the in-system precedent for a former whose level varies, and every
rule below is its shape.

### 2.1 Formation

```
⊢_L l : Level                    ⊢_L l : Level
------------------ (i ≠ v)       ------------------- (i ≠ v)
Γ ⊢_i Unit^l @ l                 Γ ⊢_i Empty^l @ l
```

`ty_infer` returns the carried `l`; `ty_check` goes back to plain `lev_eq`
with no special case. **Uniqueness of types is preserved on the nose** — this
is the whole point, see §6.1.

### 2.2 Introduction

```
⊢_L l : Level
------------------------
Γ ⊢_i ⟨⟩^l : Unit^l @ l
```

`Triv` **must** carry its level. Without it `⟨⟩` inhabits `Unit^l` for every
`l` and the non-uniqueness this route exists to avoid reappears at the term
level — the exact failure that sinks route (b) (§6.1).

### 2.3 Elimination

```
Γ ⊢_i t : Empty^{l'} @ l'    Γ, x : Empty^{l'} @ l' ⊢_i M @ l
--------------------------------------------------------------
Γ ⊢_i elim_Empty^{l, l'}(x. M; t) : M[t/x] @ l
```

`Term::ElimEmpty` currently carries **one** level (its motive's,
`typing.rs:1050`) and hardcodes the scrutinee at `Empty @ 0`. It gains a
second, `scrut_level`. This is the only variant that grows a *second* level
rather than a first.

### 2.4 Codes and decoding

```
Γ ⊢_c Unit^l : Ty l @ 1+l          El^l (Unit^l)  ⇝ Unit^l
Γ ⊢_c Empty^l : Ty l @ 1+l         El^l (Empty^l) ⇝ Empty^l
```

`TmUnit` and `TmEmpty` carry the level too, for the same reason `TmTy(l)` does:
the code is a *term*, its type `Ty l` must be determined by it, so `l` cannot
live only in the surrounding `El`.

This also repairs the half-doneness recorded in the issue — under the reverted
fix the *type* `Unit` became polymorphic while its *code* stayed at `Ty 0`, so
`El` and `Unit` disagreed about which levels exist. Here they agree by
construction.

### 2.5 Reduction

```
Vec^l(T; 0)   ⇝  Unit^l         (was ⇝ Unit — this is the fix)
Fin(0)        ⇝  Empty^0        (Fin is declared at 0; unchanged in effect)
```

`Fin` needs nothing: it is declared at level 0 and both its reducts land there.

### 2.6 Conversion

```
Unit^l ≈ Unit^{l'}   ⟸  l ≈ l'
Empty^l ≈ Empty^{l'} ⟸  l ≈ l'
```

Proof irrelevance at `Unit^l` is unchanged in force — it just keys on
`Type::Unit { .. }` rather than `Type::Unit`. Note the level comparison must be
`lev_eq` (≈), not `==`; the Static Code round already made the boxed-code path
level-equivalence-aware (§5, prerequisites).

---

## 3. Recursor branches

**Six** branches change — the spec said four before phase 2 counted them, and
missed `tm_unit`/`tm_empty`, the branches for the *encodings* `TmUnit`/
`TmEmpty`. Those are terms `Unit^l : Ty l`, so they bind a universe for exactly
the same reason `tm_ty` does. Corrected here rather than silently: the
undercount is what a spec-before-code round is for.

All six become copies of a shape `rec.rs` already has. This is the evidence the
route is with the grain rather than against it.

| branch | now | under (a) |
|---|---|---|
| `ty_unit` (`rec.rs:542`) | `univs: 0`, motive at `Level::Zero`, scrutinee `box Unit` | `univs: 1`, motive at `lvar(0)`, scrutinee `box (Unit^ℓ)` |
| `ty_empty` (`rec.rs:559`) | as above | as above, `box (Empty^ℓ)` |
| `tm_triv` (`rec.rs:1859`) | `univs: 0`, motive at `Zero`, `U_T = Unit`, scrutinee `box ⟨⟩` | `univs: 1`, motive at `lvar(0)`, `U_T = Unit^ℓ`, scrutinee `box ⟨⟩^ℓ` |
| `tm_unit` (`rec.rs:1821`) | `univs: 0`, motive at `1`, `U_T = Ty 0`, scrutinee `box Unit` | `univs: 1`, motive at `1+ℓ`, `U_T = Ty ℓ`, scrutinee `box (Unit^ℓ)` |
| `tm_empty` (`rec.rs:1840`) | as above | as above, `box (Empty^ℓ)` |
| `tm_elim_empty` (`rec.rs:1880`) | `univs: 1` (motive's ℓ); context extension hardcodes `Empty @ 0` | `univs: 2` (ℓ = `lvar(1)` motive, ℓ' = `lvar(0)` scrutinee); extension `Empty^{ℓ'} @ ℓ'` |

The template for the first three is `ty_ty` (`rec.rs:351`), which binds a
universe *precisely because* `Ty ℓ`'s level varies. `typing.rs:433` already
documents that contrast as the tell; after this round the comment describes a
uniform rule instead of an exception.

`BRANCH_DIMS` stays at **45** — no branches are added or removed, four change
shape.

---

## 4. Phases

Mirroring how [[wf-former]] was run: each phase leaves the tree green, and a
layer-`c` gate holds the line between 1 and 2.

**Phase 1 — types, terms, codes, reduction. ✅ done.** Level fields on `Type::Unit`,
`Type::Empty`, `Term::TmUnit`, `Term::TmEmpty`, `Term::Triv`; `scrut_level` on
`Term::ElimEmpty`. Through `term.rs`, `subst.rs`, `reduce.rs` (including
`Vec^l(T;0) ⇝ Unit^l` — **the bug closes here**), `typing.rs`, `conv.rs`,
`fmt.rs`. **Gate:** reject `Unit^l`/`Empty^l` for `l ≠ 0` at layer `c`, so the
unreshaped branches stay exhaustive and boxed code stays recursable over the
syntactic formers.

**Phase 2 — the six branches; lift the gate. ✅ done.** `rec.rs` as §3, plus
**`subst.rs::map_branches`** (the per-branch binder depths — missed by the
plan, and the site that fails *loudly*: a wrong universe arity indexes past
`phi` and panics in `Level::subst_at`), `BRANCH_DIMS`, both
`identity_branches` copies (`common/wt.rs` **and** `tests/typing.rs`), and
`reduce.rs`'s six `fire` call sites. Acceptance: the identity recursor
round-trips `box (Unit^ℓ)`, `box (Empty^ℓ)`, `box ⟨⟩^ℓ` and
`box (elim_Empty^{ℓ,ℓ'})` in one β-step, which is the sharp cross-check of the
new telescopes against `reduce.rs`'s `fire`.

**Phase 3 — the pins, and the coverage. ✅ done.** The pins were converted in
phase 1 (`vec_at_zero_drops_its_level_known_gap` became
`vec_at_zero_keeps_its_level`; the `known_gap` skip left
`type_reduction_preserves_level`), and `every_type_has_exactly_one_level`
passes **unchanged** — the invariant the route was chosen to preserve.

What phase 3 added:

- **The end-to-end acceptance test** (`wf.rs::polymorphic_shape`): a real
  `Wf` whose shape is `Unit^1 + Ty 0`, i.e. level 1 — a branching inductive
  with a *type* payload, which is what every polymorphic container is. `Leaf`
  builds, nested `Node`s build, the nullary arm is still proof-irrelevant, and
  `elim_Wf` computes on it. Before this round `Leaf` could not be built at all.
- **Generator coverage, which was the real gap.** The well-typed generator
  produced **no `Unit`/`Empty` at all**, so nothing in `conv_properties` or
  `ch05_06_lemmas` would have exercised this round. Now `gen_wt_type`,
  `gen_encoding` and the checked-mode intro all reach them at generated
  levels, and the scope-only generator no longer hardcodes 0.
  `vec_fin::the_well_typed_generator_reaches_unit_at_a_nonzero_level` pins it:
  measured 102 hits per 300 types, 67 of them at a non-zero level.

Adding that coverage immediately found two things, which is the point:

- `conv_pair_properties`' own `decode` and `mutate_encoding` helpers did not
  cover `TmUnit`/`TmEmpty` — they had never been generated. (`Unit^l` and
  `Empty^l` turn out to be each other's minimal mutation: same level,
  different head.)
- **Substitution is a second trigger for the box synthesis gap**
  ([[box-synthesis-gap]]), and the first found outside reduction: `δ` can
  replace a variable in an *inference* position with a payload containing a
  bare `box` (`Λ g. box ⟨⟩` under a `capp` head). Declaratively fine,
  algorithmically `NotInferable`. Skipped narrowly in
  `local_substitution_preserves_typing`, same as `conv_properties` does for
  reduction.

**Phase 4 — catch-up.** Elaborator: tier-0's nominal tag is Σ-of-Units, so
generated tags carry an inferred level. Docs:
`docs/metatheory-ch07-extensions.md` §10.3 (the LR case becomes level-indexed,
which is *simpler* than the level-polymorphic clause it currently describes),
`crates/kernel/DESIGN.md`, `docs/wf-former-design.md` §1.1 (delete the "level
defect, **open**" note).

---

## 5. Prerequisites, already paid

**Static Code (`05:1055`) had to be fixed first, and was** — 2026-07-25,
[[metatheory-lemma-sweep]]. (a) puts a level into a layer-`c` type former, so
`box (Unit^{ℓ⊔ℓ'})` and `box (Unit^{ℓ'⊔ℓ})` must compare equal. Until that
round `conv.rs` compared boxed code with plain `==`, missing the quotient
ch. 05 takes over level equivalence, and would have rejected them. (a) would
have walked straight into it — the bug was found for unrelated reasons, one
week before it would have bitten.

---

## 6. Routes not taken

Preserved costed. Both were live at decision time; neither was rejected for
being unsound.

### 6.1 (b) — layer-gate the polymorphism to `p`/`m`

*Keep one `Unit`, but let it check at any level at layers `p`/`m`, pinned to
`0` at layer `c`.* The argument: ch. 04 §Non-cumulativity's case for
uniqueness is entirely about the code eliminator, and `box` checks its body at
layer `c`, so uniqueness is only *needed* there.

**Metatheologically clear.** Verified this session and worth not re-deriving:

- **No Tarski-completeness requirement exists.** ch. 08 read in full
  (Injectivity `08:19`, Consistency `08:48`, Conversion `08:96`,
  Convertibility `08:226`, Decidability `08:239`/`:357`) — all structural
  induction on derivations, none quantifying over "all types at level `l`".
  ch. 07's Neutral Types law (`07:239`) builds `El l ν ≈ El l' ν'` *from* the
  code relation: a closure rule, not completeness. So (b) creating `Unit @ 1`
  at `p` with no code at `Ty 1` breaks nothing stated.
- **A layer-`c` term legitimately has a layer-`p` type.** The paper's
  global-context rule (`04:~985`) admits `u : Trm_i(Δ ⊢ T @ l)` for
  `i ∈ {v, c}` while checking `T` at layer **p**, and ch. 05's coverage lemmas
  conclude their type equivalences at `p` (`05:1573`, `:1576`).
  `typing.rs:154` already matches. So (b)'s `c`/`p` asymmetry sits in a gap the
  system has deliberately.
- **The LR never inverts on a level.** Its only two "must be unique" appeals
  (`07:761`, `07a:1092`) are to determinacy of `⇝*`.

**Why it was rejected anyway.** Probing, not argument:

1. **(b)-as-specified does not fix the motivating problem.** It patches
   `ty_check` — *types*. The nullary-constructor inhabitation failure of §1 is
   in `tm_check`'s fallback (`typing.rs:689`): `Triv` infers level 0, is
   checked against `l`, `lev_eq` fails. `Leaf` still cannot be built.
2. **The repair costs the sentence (b) advertised keeping.** Making (b) work
   requires special-casing `Triv` too, so `⟨⟩ : Unit @ l` for every `l` at
   `p`/`m`. Ch. 04 says *"each term has a unique type"* — literally about
   **terms**. (b) looked like it preserved that only because it never touched
   terms. Working (b) abandons exactly that sentence at `p`/`m`.
3. **Cost was understated 5×.** "Roughly two lines" is ~10 across two
   judgments, and `infer_type`/`infer_term` stop being "the level" and become
   "the *least* level" — a permanent qualification on two public functions.

**What would reopen it:** evidence that (a)'s elaborator churn (every
`Unit`/`⟨⟩` carrying an inferred level, tier-0 tags included) is materially
worse than expected. That is a measurement, and phase 4 is where it would show.
Nothing metatheoretic reopens (b); that question is closed.

### 6.2 (c) — `Vec^l(T; 0)` as its own proof-irrelevant whnf

*Do not reduce at length 0 at all: make `Vec` at 0 a normal (non-neutral) type
carrying `Unit`'s irrelevance directly in `conv.rs`. Levels never move.*

Rejected, and it was the weakest of the three throughout:

- Costs a logical-relations case for `Vec` after all, undoing phase 4's
  strongest result — that `Vec`/`Fin` need **no** LR case
  (`docs/metatheory-ch07-extensions.md` §10).
- Costs an *introduction* rule: `⟨⟩` must inhabit `Vec^l(T;0)`, which gives
  `Triv` two types and reintroduces precisely the non-uniqueness (a) and (b)
  exist to avoid — unless `Triv` is annotated, at which point you have paid
  most of (a) without getting `Unit^l`.

Recorded so it stays costed. Do not relitigate without a new argument about
the LR case.

---

## 7. Decision, and what would change it

**(a), 2026-07-25.** In order of weight:

1. **(b) does not solve the motivating problem as specified**, and the repair
   that makes it solve it breaks ch. 04's actual sentence at `p`/`m`.
2. **(a)'s inhabitation story is by construction.** `⟨⟩^l : Unit^l @ l` needs
   no special case anywhere; §1's hole closes because the rule closes it.
3. **(a)'s cost is bounded, mechanical, and templated.** `ty_ty` is already the
   shape all four branches become — checkable evidence rather than taste.

Against, and accepted: it is a phase-3-sized round, and it pushes level
annotations into the elaborator.

**What would change it:** phase 4 measuring elaborator churn as materially
worse than expected would reopen §6.1 — on ergonomics, not on metatheory.
