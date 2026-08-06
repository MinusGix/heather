---
title: Type-motive level slots are observable only by a bundle whose bodies use them
status: open
labels: [kernel,soundness,testing]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/rec.rs @ HEAD
---

The residue of [[branch-telescope-entries-unchecked]], and the successor to
its second follow-up — scoped *down* from "52 hand-written level slots for
all branches" to the type-motive-derived entries only, since the
term-motive half is now covered by formation.

## Why

The generic well-formedness check pins every term-motive entry's `ℓ` slot:
`M_Trm[l/ℓ, …, U/U_T, …]` instantiates to `□(g ⊢ U @ l)`, and formation
forces the two slots to agree. Type-motive entries do not have that
property: `M_Typ[l/ℓ, …]` instantiates to `□(g ⊢ Ty l)`, which is well
formed for *any* in-scope `l` — the level's scope is checked, its value is
not. Probed, not assumed: mutating `ty_pi`'s `x_S` slot from `ℓ` to `ℓ'`
leaves the generic check green.

And no motive can fix it. `x_T` occurs in `M_Typ` only as a local of
contextual type, and there is no type-level unboxing, so `ℓ` and the `x_T`
payload can never meet inside the motive. A wrong level slot on
`x_S`/`x_T`/`x_M` is invisible to every formation check and observable only
at a *use site*: a branch bundle whose bodies actually use those recursive
calls, checked under an `ℓ`-dependent motive.

## What

A test bundle under an `ℓ`-dependent, payload-independent type motive, with
branch bodies that route through `x_S`/`x_T`/`x_M` the way
`tests/typing.rs::elim_empty_branch_recursive_call_is_at_the_scrutinee_level`
routes through `x_t`. Scope: the type-motive-derived entries of the
structural branches (`ty_pi`/`ty_sigma`/`ty_w`/… `x_S`, `x_T`; the
eliminator branches' `x_M`).

The falsifier already exists and must be the polarity check: `ty_pi`'s
`x_S` level slot `lvar(1)` → `lvar(0)` passes every test today and must
fail under the new bundle.

## When

Before the Coq formalization transcribes the `G_Typ` table; or the next
time a level slot in a type-motive entry is edited for any reason.
