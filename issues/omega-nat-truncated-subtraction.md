---
title: omega reads Nat subtraction as an atom: split a - b like Lean's omega
status: closed
labels: [omega,tactics,arithmetic]
area: tactics
created: 2026-10-29
updated: 2026-10-30
---

`omega` reads a truncated Nat subtraction `a - b` as one atom, so the facts
that tie it to `a` and `b` have to be handed in by hand. Probe on master
4f0ac27 (2026-10-29, [[proof-patterns-audit-2026-10]]):

```
theorem natsub(a, b: Nat, h: b <= a): a - b + b = a { omega }
```

is refused: `CutSat's integer model [b = 0, a = 0, nat::Nat::sub(a, b) = 1]`.
Every round that met it wrote the same workaround, a
`Nat::sub_add_cancel` fact as a `let` beside the call (cat's spec proof,
S4's call frames, the native Wp `d - 8`, finite sums), and memory recorded
it as a rule of thumb rather than a gap.

Lean's `omega` handles `a - b` at Nat by introducing the atom `t` with the
case split `b <= a ∧ t + b = a ∨ a < b ∧ t = 0`. Here the split has an
owner already: CutSat splits disequalities only when cornered
([[cutsat-first-class-relations]] is the neighbouring work), and the
certificate is a scoped DAG with one `have` per node, so a two-case
subtraction split is one more scope kind.

## Acceptance

- The probe above closes with a bare `omega`, and the same at `a - b <= a`
  and `a < b → a - b = 0`.
- A control where the truncation matters (`a - b + b = a` without `b <= a`)
  is refused with a model that names the case.
- The library's hand-fed `sub_add_cancel` lets next to an `omega` can be
  dropped (not required to land; a sweep can follow).

## Landed (2026-10-30)

`omega` splits `a - b` as Lean's does: `omega::nat_sub_elim` (omega.hthr)
gives the branches `b <= a ∧ (a - b) + b = a` and `a < b ∧ a - b = 0`, each
closed by `omega` again, the subtraction kept one atom
(`split_nat_subtraction`, the last fallback of the attempt that answers).
Design: `docs/omega-measure-reduction-design.md` §16. Probes
`sub_add_cancel_bare`, `sub_le_bare`, `sub_zero_past`, `sub_in_fact`,
`sub_nested`, `sub_checking` and the control `sub_add_cancel_truncated`
(refused, its report naming `__omega_sub0_case: Lt(a, b)`) are in
`lib/_tests/std/tactic/omega_tests.hthr`. The library sweep is
[[omega-sub-add-cancel-sweep]]; `Format::gamma_at` was the first drop.
