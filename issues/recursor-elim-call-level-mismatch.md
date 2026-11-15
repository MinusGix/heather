---
title: Code-recursor elim branches declare the scrutinee's recursive call at the motive's level
status: closed
labels: [kernel,delam,metatheory,soundness]
created: 2026-08-06
updated: 2026-08-06
code: crates/kernel/src/rec.rs @ HEAD
---

The code recursor's eliminator branches declared the scrutinee's recursive
call at the *motive's* universe level, while reduction supplies it at the
*scrutinee's*. Found while transcribing the declarative rules
([[delam-extensions-writeup]], `docs/kernel/delam-extensions.md` §7.7 / §16.1).

## Why

`elim^Trm(l, Δ, T, t) : M_Trm[l/ℓ, Δ/g, T/U_T, t/x_t]` where `l` is the
level of `T` — `typing.rs`'s `ElimCodeTm` checks `ty` at `code_level` and
instantiates the motive with it, so the `ℓ`-slot *is* the type's level, by
construction. A recursive call on a sub-structure of type `X @ l_X` must
therefore instantiate `ℓ` at `l_X`.

`t_elimE`'s scrutinee has type `Empty^{ℓ'} @ ℓ'`, so `x_t` must be declared
at `M_Trm[ℓ'/ℓ, …]`. The kernel declared it at `M_Trm[ℓ/ℓ, …]` — the
motive's level — against a β rule supplying
`elim^Trm(scrut_level, Δ, Empty^{scrut_level}, scrut)`.

This is inherited from ch. 04. `t_elimN` writes `M_Trm[ℓ/ℓ, …, Nat/U_T, …]`
where its own neighbours `t_ze` and `t_succ` write `0/ℓ` for the *same*
`Nat/U_T` slot, and `t_El` writes `1 + ℓ/ℓ` for a `Ty ℓ`-typed one. The
paper contradicts itself in adjacent rules; `ℓ/ℓ` is a typo, which the
kernel transcribed and then repeated twice when `Empty` and `sEmpty` were
level-indexed. Filed so [[metatheory-lemma-sweep]] and the Coq
formalization do not transcribe the flaw as scripture.

## What

Corrected rule (`docs/kernel/delam-extensions.md` §7.7):

    x_t : M_Trm[ℓ'/ℓ, g/g, Empty^{ℓ'}/U_T, box u_t^id / x_t] @ l₂

Three sites, all in `crates/kernel/src/rec.rs`: `tm_elim_nat`'s `x_t`
(`Nat @ 0`, so `0/ℓ`), `tm_elim_empty`'s and `tm_elim_sempty`'s (`ℓ'/ℓ`).
Every other recursive-call binder was audited against its `reduce.rs`
counterpart and is correct — `tm_case` (`ℓ⊔ℓ'`), `tm_j`, `tm_elim_w`,
`tm_elim_wf`, `tm_transp`, `tm_supf` and all constructor/encoding branches.
Only the eliminators whose scrutinee sits at a level the motive does not
share were wrong.

**Why it stayed latent, precisely.** Not just "no live motive distinguishes
the levels". Under the identity motives the old entry is *ill-formed*:
`M_Trm[ℓ/ℓ, Empty^{ℓ'}/U_T, …]` is `□(g ⊢ Empty^{ℓ'} @ ℓ)`, and
`Empty^{ℓ'}` does not live at `ℓ`. Nothing well-formed could be checked
against it, so no branch could use its own recursive call and no error ever
surfaced. The defect is still real: with an `ℓ`-dependent, `U_T`-independent
motive such as `M_Trm := □(g ⊢ Ty ℓ)` the old entry *is* well-formed, a
branch body of `x_t` typechecks at the motive's level, and reduction hands
it a term at the scrutinee's — subject reduction fails. That telescope
entries can be ill-formed without anything checking is its own hole:
[[branch-telescope-entries-unchecked]].

## Done

`tests/typing.rs::elim_empty_branch_recursive_call_is_at_the_scrutinee_level`
— the missing observer. Every existing bundle's `t_elimE` body ignores
`x_t`, so its declared type was never looked at; this one routes the
identity body through `λ(z : dom). box (elim_Empty …)` applied to `x_t` and
varies only `dom`:

- `□(g ⊢ Empty^{ℓ'} @ ℓ')` — accepted, and the identity round-trip still
  fires in one β-step. Fails with `NotConvertible` against the old rule.
- `□(g ⊢ Empty^ℓ @ ℓ)` — a well-formed contextual type, but not this
  scrutinee's: rejected.
- `□(g ⊢ Empty^{ℓ'} @ ℓ)` — the old declaration verbatim: rejected as not
  a type at all, which is the latency argument above, pinned.

`ℓ` and `ℓ'` are distinct universe *variables* of the telescope, so no
instantiation can collapse the two readings. Suite 1133 → 1134, all green;
no golden number moved. `docs/kernel/delam-extensions.md` §16.1 carries the
resolution and the ill-formedness finding. The `t_elimN`/`t_elim_sE`
siblings are fixed by the same argument but have no bespoke witness — the
generic check in [[branch-telescope-entries-unchecked]] is the intended
cover.
