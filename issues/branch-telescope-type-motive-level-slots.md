---
title: Type-motive level slots are observable only by a bundle whose bodies use them
status: closed
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

## Done

Two observers, and the cheap one is the general one.

`crates/kernel/src/rec.rs` — a `#[cfg(test)]` walk pinning all **45**
type-motive recursive calls across **27** branches, with no transcribed
level or context anywhere. The premise above — that only a use site can
see these slots — is true of *semantic* observation and false of
observation: the branch's own **global bindings** already know every
answer. A type-motive call is the call on a sub-*code*, every sub-code a
branch destructures is bound as a layer-c `Typ_c(Δ_k, l_k)` global,
`fire` hands the *same* payload to both slots, and `typing.rs` types
`elim^Typ(l, Δ, box X)` at `M_Typ[l/ℓ, Δ/g, …]` — so the call's `(Δ, l)`
*must* be the binding's. The check therefore cross-validates the two
independently hand-written halves of each `BranchSpec` against each
other, and the half it anchors to is one the identity branch bodies and
the round-trip tests already exercise against reduction.

**The correspondence turned out to be an exact order-preserving
bijection in all 52 branches**: the i-th type-motive local ⟺ the i-th
layer-**c** `Ty` global. The exception is the paper's own
(`docs/delam-extensions.md` §16.5) — a `Typ_p` binding is an *external
index*, not a sub-code, and carries no call: exactly `t_x`'s and `t_λ`'s
`U_T`, because a `λ` does not store its codomain. A `covered == 45`
tripwire fires if any branch gains or loses a call. The invariant is
sharp enough to be a runtime check if the tables ever go dynamic — logged
at [[rec-ga-runtime-telescope-check-decision]].

`tests/typing.rs::type_motive_branch_entries_are_usable_at_their_declared_context_and_level`
— the use-site half kept for three representative slots (`ty_pi`'s `x_S`
and `x_T`, `tm_elim_empty`'s `x_M`), the `elim_empty…` λ-annotation
pattern generalised, with four negative controls. One structural
insight makes it nearly free: `rec_ga` checks all 52 branches whatever
the scrutinee is, so a single `elim^Typ` on `box Nat` observes any
branch's telescope — no per-branch scrutinee needed.

The **context** slots turned out to be unchecked in precisely the same
way as the levels (`□(g ⊢ Ty ℓ')` is well formed, just not the
codomain's call), so both are now covered; a `ty_pi` `x_T` ctx
`g_x → g` mutation is caught by name.

Polarity, five mutations, each restored: the mandatory `ty_pi` `x_S`
`ℓ → ℓ'` — which, confirmed by running the suite under it, **fails
nothing else at all**; `tm_elim_empty`'s `x_M` and `tm_case`'s `x_M`
(the eliminator motives); the `ty_pi` `x_T` context slot; and the
use-site test's own three controls. No slot is currently wrong. Suite
1135 → 1137, full `scripts/test` green, no golden number moved.

**Residue.** 35 of the 45 slots have a declarative rule to check the
*binding* against; **10 do not** — the `Vec`/`Fin`/`Wf`/`sEq`/`sEmpty`
branches are §17 "deliberately not covered", so for those the kernel is
still its own only specification: [[uncovered-formers-recursor-rules]].
The Coq `G_Typ` transcription should take the round's enumeration table
as the checklist and treat those ten as unattested. A tooling snag
noticed en route — cargo's cross-target fail-fast hiding a co-failing
integration test — is filed at [[scripts-test-fail-fast]].
