---
title: "Level-index Unit^l/Empty^l: close the Vec^l(T;0) level drop"
status: open
labels: [kernel,levels,metatheory,delam]
created: 2026-07-25
updated: 2026-07-25
code: crates/kernel/src/typing.rs:441 @ fd72716
---

DeLaM ch. 06 states, as a lemma rather than an assumption:

> **Lemma (Preservation).** If `⊢_i T @ l` and `T ⇝ T'`, then `⊢_i T' @ l`.
> If `⊢_i t : T @ l` and `t ⇝ t'`, then `⊢_i t' : T @ l`.

at the **same** `l`. Ch. 07's logical relations depend on it: every type rule
of §sec:dt:klogrel begins `T ⇝* W @ l`, and the auxiliary judgment
`\ttypreds i T W l` is *defined* as `⊢ T @ l` plus `T ⇝* W` — it carries `l`
across the reduction and the LR reads the whnf at that same `l`.

**We violate the type half.** `Vec^l(T; 0) ⇝ Unit`, and `Unit` is fixed at
level 0, so for every `l ≠ 0`:

```
⊢ Π^{1,0}(_ : Vec^1(Ty 0; 0)). Nat @ 1        well-formed
  ⇝  Π^{1,0}(_ : Unit). Nat                   LevelMismatch
```

`Vec` is the kernel's first type former whose weak head normal form is chosen
by a **term**. `El` is chosen by a term too, but its term is a code carrying
its own level, so `El` cannot drop one; `Vec`'s length is a bare `Nat` and at
`0` the reduct has nothing to do with `l`. The successor case preserves `l`
exactly (`Σ^{l,l}`), and `Fin` is unaffected — declared at `0`, both reducts
land at `0`. So the defect is exactly one reduction rule.

Found by the phase-4 ch. 07 pass of [[wf-former]], while writing the
fundamental-theorem arm for `Vec`-formation, which needs `Unit ~ Unit @ l`
and had nothing to land on.

## Why the obvious fix is wrong

Making `Unit`/`Empty` level-polymorphic in formation (`⊢ Unit @ l` for any
well-formed `l`) repairs preservation in one line. **It was landed in
`fd72716` and reverted in the same session** — it breaks something the paper
is explicit about.

DeLaM ch. 04 §Non-cumulativity:

> "When we split code into cases in the elimination form, we must specify in
> each case how do we construct the original code from its components.
> Therefore, it is the most convenient, when **each term has a unique type**,
> leading to a conclusion of preferring non-cumulative universes."

and, on universe polymorphism, that a term's level "must be uniquely
determined due to non-cumulativity". Uniqueness is load-bearing *for the code
eliminator*, which is the most delicate machinery in the system.

`box T : □(Δ ⊢ Ty l)` is **checking-only** (`typing.rs`, `Term::BoxTy`) and
checks `T` at `l` via `ty_check`. So a type that checks at many levels is a
*term* with many types. Measured, with the polymorphic version in place:

```
box Unit  : CodeTy(level 0) -> Ok      box Nat : CodeTy(level 0) -> Ok
box Unit  : CodeTy(level 1) -> Ok      box Nat : CodeTy(level 1) -> LevelMismatch
box Unit  : CodeTy(level 2) -> Ok
box Empty : CodeTy(level 0/1/2) -> Ok all
```

And the recursor comes apart, because the branch tables were built against
uniqueness. From `rec.rs`:

| branch | `tele.univs` | motive instantiated at |
|---|---|---|
| `ty_ty` | **1** | `Level::succ(lvar(0))` — `Ty ℓ`'s level varies |
| `ty_nat` | 0 | `Level::Zero` |
| `ty_unit`, `ty_empty` | 0 | `Level::Zero` |

`ElimCodeTy` returns the motive at `code_level`; the `ty_unit` branch is
checked at the motive at `0`. With polymorphic `Unit`, measured:

```
elim(code_level=1; box Unit) : CodeTy(1)  ->  Ok      <- impossible before
   reduct box(Unit): at claimed CodeTy(1) -> Ok; at branch-checked CodeTy(0) -> Ok
elim(code_level=1; box Nat)               ->  LevelMismatch
```

So the redex is typed at `M[1/ℓ]` while the branch it fires into was verified
at `M[0/ℓ]`. For the *identity* motive the reduct survives — `box Unit` now
inhabits both, which is the same polymorphism masking its own damage. For any
motive genuinely depending on `ℓ` whose branch term is not itself
level-polymorphic (e.g. `M_Typ := Ty ℓ`, branch a code at `Ty 0`), it does
not. **Preservation for the code recursor breaks.**

Probably not exploitable into an inhabitant of `Empty` — the system has no
elimination for levels, so you cannot build a motive that is `Unit` at `ℓ=0`
and `Empty` at `ℓ=1`. Same character as the `Vec` bug itself: a broken lemma,
not an exploit. That is not a reason to keep it.

Note the half-doneness that is itself a tell: the *type* `Unit` became
polymorphic while its *code* `TmUnit : Ty 0` did not (`TmUnit : Ty 1` is
still rejected), so `El` and `Unit` disagreed about what levels exist.

## Decision (2026-07-25): route (a), level-indexed `Unit^l` / `Empty^l`

**Rules, phases and the full costed record of the routes not taken:
`docs/unit-empty-level-indexing.md`** (written before the code, house pattern).

Parameterize rather than polymorphise: `Unit^l : Type @ l`, distinct types at
distinct levels, as non-cumulative systems do it. Uniqueness of types survives
on the nose, `ty_check` goes back to plain `lev_eq`, `Vec^l(T;0) ⇝ Unit^l`
preserves the level, and the four affected recursor branches become copies of
`ty_ty` — which binds a universe precisely because `Ty ℓ`'s level varies.

### What settled it, beyond the original write-up

The gap is **not only a broken lemma — it is a functional hole.** Measured:

```
Vec^1(Ty 0;0) well-formed @1 : Ok
  ..its whnf                 : Unit
Triv : Vec^1(Ty 0;0) @ 1     : Err(LevelMismatch)
Triv : Vec^1(Ty 0;0) @ 0     : Ok
```

`Vec^l(child; 0)` is the children type of a **nullary constructor** of a `Wf`
whose shape is at level `l`. So `Leaf` cannot be built for any polymorphic
branching inductive today. Monomorphic ones are unaffected (shape at level 0),
which is why this hid from phase 1 to phase 4 of [[wf-former]].

And (b) does **not** fix it: (b) patches `ty_check` (types), while the
inhabitation failure is in `tm_check`'s fallback (`typing.rs:689`) — `Triv`
infers level 0 and `lev_eq` rejects it against `l`. The repair requires
special-casing `Triv`, i.e. `⟨⟩ : Unit @ l` for every `l` at `p`/`m` — and
ch. 04's sentence is literally *"each term has a unique **type**"*. (b) looked
like it preserved that only because it never touched terms.

### Phases

| | Phase | State |
|---|---|---|
| 1 | level fields + reduction; layer-`c` gate. **The bug closed here** | **done** |
| 2 | the **six** recursor branches (four predicted, plus `tm_unit`/`tm_empty`); lift the gate | **done** |
| 3 | pins, the polymorphic end-to-end acceptance test, and generator coverage | **done** |
| 4 | elaborator catch-up (tier-0 tags are Σ-of-Units) + docs | next |

### Prerequisite, already paid

**Static Code (`05:1055`)**, fixed 2026-07-25 by [[metatheory-lemma-sweep]].
(a) puts a level into a layer-`c` type former, so `box (Unit^{ℓ⊔ℓ'})` and
`box (Unit^{ℓ'⊔ℓ})` must compare equal; until that round `conv.rs` compared
boxed code with plain `==` and would have rejected them. Found for unrelated
reasons, one week before it would have bitten.

### Routes not taken

**(b) layer-gate to `p`/`m`** and **(c) `Vec^l(T;0)` as its own irrelevant
whnf** are preserved fully costed in `docs/unit-empty-level-indexing.md` §6,
including the metatheory verification that cleared (b) (no Tarski-completeness
requirement anywhere in ch. 07/08; a layer-`c` term legitimately has a layer-`p`
type; the LR never inverts on a level). **Neither was rejected for being
unsound.** Only one thing reopens (b): phase 4 measuring (a)'s elaborator churn
as materially worse than expected — ergonomics, not metatheory. (c) needs a new
argument about the LR case.

## Current state of the tree

- The kernel is at the **pre-fix** behaviour: `Unit`/`Empty` fixed at `0`,
  every type single-levelled, `box Unit` single-typed. The `Vec` gap is open.
- `crates/kernel/tests/vec_fin.rs::vec_at_zero_drops_its_level_known_gap`
  pins the gap so it cannot close or widen silently.
- `crates/kernel/tests/vec_fin.rs::every_type_has_exactly_one_level` pins the
  invariant any fix must preserve, including the `box` consequence.
- `crates/kernel/tests/conv_properties.rs::type_reduction_preserves_level` is
  the missing property (below), live, skipping only this reduct with only this
  error.
- `crates/kernel/src/typing.rs::ty_check` carries the warning in its doc
  comment so the next person to reach for the one-line fix reads why not.

## The deeper finding: a missing property, not a missing case

`conv_properties.rs` had `reduction_preserves_type` — the **term** half of
ch. 06's lemma — and no type half. That is the whole reason this survived
since phase 1. The generator was producing the witness all along: `gen_wt_type`
takes `Vec`'s level from its element (so `l > 0` is routine) and picks a small
literal length two times in three (so `0` is routine). The witness was
generated hundreds of times per run and nothing looked at it.

`type_reduction_preserves_level` now exists and fails on **seed 102** with the
kernel reverted — first run, no tuning. Both halves of a paper lemma are worth
having; half of one is a blind spot shaped exactly like the lemma's other half.

**The sweep is done: [[metatheory-lemma-sweep]]**, audit in
`docs/ch05-06-lemma-audit.md`. All 53 lemma environments of ch. 05/06 with a
verdict each; nine new property tests. It found the same shape twice more —
the *type* half of ch. 06's Soundness (`06:148`) was missing next to the term
half, one lemma before Preservation, and the suite's own generator-soundness
oracle was a single 300-case stream standing in for a precondition ten property
tests depend on (it was violated at 1 in 3000). Determinacy turned out to hold
by construction; the residue that does not — `step(t).is_none() ⟺ is_whnf(t)`,
two independent copies of the `Vec`/`Fin` stuck-length condition — is now
checked.

Also from the sweep, for candidate (b) below: **no Tarski-completeness claim
appears in the paper.** See [[metatheory-lemma-sweep]] for the citations. That
is evidence for (b), not a green light — ch. 08 is still unread.

## Log

- 2026-07-25: Filed. Found by the [[wf-former]] phase-4 ch. 07 pass; the
  one-line `Unit`-polymorphism fix was landed in `fd72716`, shown to break
  type uniqueness at `□` and code-recursor preservation, and reverted in the
  following commit. Kernel is back to the pre-fix behaviour with the gap
  pinned by tests and the missing property added. Fix (a) is the recommended
  direction; (b) is cheaper but gated on the Tarski-completeness question.
- 2026-07-25: The sweep this issue asked for is done: [[metatheory-lemma-sweep]], audit at docs/ch05-06-lemma-audit.md. Relevant to this issue specifically: (i) candidate (b)'s gating question — does anything require every layer-p type at level l to have a code at Ty l — was checked against the paper and NO Tarski-completeness claim exists. 'Tarski' occurs five times in ch. 04 (04:96-120, :203, :781), always about the separation of types from terms and why Russell-style universes cannot state the indices of code, never a surjectivity property; and ch. 07's term relation at Ty l (07:512-514) is by cases on the code whnf, saying which codes are related, never that every related type is an El. Evidence for (b), NOT a green light: ch. 08's decidability argument is still unread, and so is our own 'boxed code stays exhaustively recursable' invariant, which is ours and not the paper's. (ii) The audit ranks ch. 05 Static Code (05:1055) as the top remaining gap, and it is the one that bears on this decision — at layers v/c convertibility must BE syntactic identity modulo level equivalence, which is what makes the code eliminator's intensional analysis meaningful. Only hand-built instances today. Worth closing before choosing between (a) and (b). (iii) ch. 05's Lifting lemma is now machine-checked (p->m arm), which the sweep needed in order to justify a generator fix.
- 2026-07-25: Both of (b)'s open questions are now closed by reading ch. 08 in full and ch. 06's normal-form grammar; details and citations in docs/ch05-06-lemma-audit.md and [[metatheory-lemma-sweep]]. (b) is NOT blocked by the metatheory: nothing in ch. 08 (Injectivity 08:19, Consistency 08:48, Conversion 08:96, Convertibility 08:226, Decidability 08:239/08:357) requires every layer-p type at level l to have a code at Ty l, and ch. 07's Neutral Types law (07:239) is a closure rule building El l v ~ El l' v' FROM the code relation rather than a completeness statement. A stronger structural argument FOR (b) turned up: the paper's global-context rule (04:~985) admits u : Trm_i(Delta |- T @ l) for i in {v,c} while checking T at layer p, and ch. 05's coverage lemmas conclude their type equivalences at p (05:1573, :1576), so a layer-c term legitimately has a layer-p type — the c/p asymmetry (b) introduces sits in a gap the system already has deliberately, rather than being new. typing.rs:154 already matches. Also: the LR's only two 'must be unique' appeals (07:761, 07a:1092) are to determinacy of multi-step reduction, not to a type determining its level, so nothing semantic needs level uniqueness at p. AGAINST (b), and this is now the actual cost and it is design rather than soundness: (b) falsifies vec_fin::every_type_has_exactly_one_level and the new ch05_06_lemmas::inferred_level_is_the_only_level, both of which quantify at layers p/m, so both would have to be re-scoped to layer c; and infer_type stops being a deterministic level oracle at p for Unit/Empty, which is a direct input to [[elab-unifier-completeness]]'s level inference. Net: (a) and (b) are now a genuine choice on cost rather than (b) being gated. Recommendation unchanged pending ch. 05 Static Code (05:1055), which the audit ranks first and which bears directly on this decision.
- 2026-07-25: ch. 05 Static Code (05:1055) is now machine-checked ([[metatheory-lemma-sweep]]), and it did NOT discriminate (a) from (b) the way I predicted it would. What it did instead: it found a live kernel defect and removed a landmine specific to (a). conv.rs compared boxed code with plain == , while the lemma quotients its equalities over level equivalence and gives its own example (Ty(l u l') and Ty(l' u l) are EQUAL as code) — so the kernel rejected that pair verbatim. Fixed with Type/Term::normalize_levels. Bearing on this decision: (a) puts a level into a layer-c type former, so box(Unit^{l u l'}) vs box(Unit^{l' u l}) has to compare equal; before the fix it would not have, and (a) would have walked straight into it. (b) leaves layer c untouched and was never exposed. So (a) is now safer to build than it was, and the choice between (a) and (b) still rests on what the earlier log entry recorded: (b) is unblocked metatheoretically but costs level-uniqueness at layer p and deterministic level inference for Unit/Empty; (a) is faithful but phase-3-sized. Also worth noting from writing the test: a pair of codes at inequivalent levels but the SAME code type cannot be constructed at all, because box(Delta |- Ty l) fixes l and at layer c a type determines its level. That is uniqueness of types showing up as a limit on what is even expressible — a small piece of evidence that the layer-c half of the invariant is doing real structural work, which is the half both (a) and (b) preserve.
- 2026-07-25: DECIDED: route (a), level-indexed Unit^l/Empty^l. Rules, phases and the costed record of what was not taken are in docs/unit-empty-level-indexing.md, written before the code in the house pattern. Two things settled it beyond the original write-up. FIRST, the gap is not only a broken lemma but a functional hole: Vec^l(child;0) is the children type of a NULLARY CONSTRUCTOR of a Wf whose shape sits at level l, and measured on the current kernel, Vec^1(Ty 0;0) is well-formed at 1, its whnf is Unit, and Triv : Vec^1(Ty 0;0) @ 1 is LevelMismatch while @ 0 is Ok — so Leaf cannot be built for any polymorphic branching inductive. Monomorphic ones are unaffected (shape at level 0), which is exactly why this hid from phase 1 to phase 4 of [[wf-former]]. SECOND, (b) does not fix that: (b) patches ty_check, i.e. TYPES, while the inhabitation failure is in tm_check's fallback at typing.rs:689 where Triv infers level 0 and lev_eq rejects it against l. Making (b) work requires special-casing Triv as well, i.e. <> : Unit @ l for every l at layers p/m — and ch. 04's sentence is literally 'each term has a unique type'. (b) appeared to preserve that sentence only because it never touched terms; the working version abandons precisely it. Cost was also understated about 5x (~10 lines across two judgments, and infer_type/infer_term permanently become 'least level' rather than 'the level'). (b) was NOT rejected for being unsound — the metatheory verification cleared it and is preserved in the doc. Only ergonomics reopens it: phase 4 measuring (a)'s elaborator churn as materially worse than expected. Phases: 1 level fields + reduction with a layer-c gate (the bug closes here), 2 the four recursor branches ty_unit/ty_empty/tm_triv/tm_elim_empty and lift the gate, 3 close the pins plus a polymorphic nullary-arm acceptance test, 4 elaborator catch-up (tier-0 tags are Sigma-of-Units) and docs. Prerequisite already paid: the Static Code fix from [[metatheory-lemma-sweep]], without which box(Unit^{l u l'}) vs box(Unit^{l' u l}) would have been rejected — found for unrelated reasons one week before it would have bitten.
