---
title: "Vec^l(T;0) ⇝ Unit drops the level: fix it without breaking type uniqueness"
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

## Candidate fixes

### (a) level-indexed `Unit^l` / `Empty^l` — most faithful

Parameterize rather than polymorphise: `Unit^l : Type @ l`, distinct types at
distinct levels, exactly as non-cumulative systems do it (Agda's
`record ⊤ {ℓ} : Set ℓ`). Uniqueness is preserved on the nose, `ty_check` goes
back to plain `lev_eq`, and `Vec^l(T;0) ⇝ Unit^l` preserves the level.

Crucially the recursor branches get the shape they already have for `Ty`:
`ty_unit`/`ty_empty` become `univs: 1`, motive at `lvar(0)`, scrutinee
`box (Unit^ℓ)` — a copy of `ty_ty`. That is evidence this is the grain of the
design rather than against it.

Cost, and it is a phase-3-sized round: level fields on `Type::Unit`,
`Type::Empty`, the codes `TmUnit`/`TmEmpty`, and the intro/elim forms that
name them (`Triv`, `ElimEmpty`) — otherwise `⟨⟩` inhabits `Unit^l` for every
`l` and the disease returns at `tm_triv`. Then `BRANCH_DIMS`, both
`identity_branches` copies, both generators, `subst`, `conv`, `fmt`, `reduce`.
The LR case for `Unit` becomes level-indexed, which is *cleaner* than the
level-polymorphic clause §10.3 of the ch. 07 doc currently describes.

### (b) layer-gate the polymorphism — cheapest, needs one question answered

Uniqueness is only *needed* at layer `c` (§4's argument is entirely about the
code eliminator), and `box` checks its body at layer `c`. So: `Unit`/`Empty`
level-polymorphic at layers `p`/`m`, fixed at `0` at layer `c`. Then
`box Unit` stays single-typed, `Vec^1(T;0) ⇝ Unit` is fine at `p`, and code
of `Vec^1(T;0)` dispatches to `ty_vec` (which binds a universe already) and
never reaches `ty_unit`. Conversion never runs at layer `c`, so nothing
reduces there. Roughly two lines.

**The question to answer first:** does anything require every layer-`p` MLTT
type at level `l` to have a code at `Ty l`? (b) creates `Unit @ 1` at `p` with
no code at `Ty 1`. If Tarski-universe completeness is claimed or relied on
anywhere — ch. 07's universe case, ch. 08 — (b) is out.

**Partly answered** by [[metatheory-lemma-sweep]]: no Tarski-completeness
claim exists in the paper (citations in that issue). Still **not** a green
light — ch. 08's decidability argument is unread, and the kernel's own "boxed
code stays exhaustively recursable" invariant is ours, not the paper's, so it
has to be argued separately. Do not implement (b) before both.

### (c) `Vec^l(T;0)` is its own whnf, proof-irrelevant

Don't reduce at `0` at all: make `Vec` at length `0` a normal (non-neutral)
type with `Unit`'s irrelevance directly in `conv.rs`. Levels never move.

Costs an LR case for `Vec` after all (undoing the "no LR case" result of
`docs/metatheory-ch07-extensions.md` §10) and, worse, an introduction rule —
`⟨⟩` must inhabit `Vec^l(T;0)`, which gives `Triv` two types and reintroduces
exactly the uniqueness problem (a) and (b) exist to avoid, unless `Triv` is
annotated. Weakest of the three; recorded so it stays costed.

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
