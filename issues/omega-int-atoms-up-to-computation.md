---
title: omega keys Int atoms by spelling: the Nat side's computation step is not mirrored
status: closed
labels: [omega,proofs,elaboration,ergonomics]
created: 2026-09-27
updated: 2026-09-27
---

[[omega-atoms-up-to-computation]] made Nat atoms equal up to computation: a
Nat atom that computes to a numeral is that constant, and one that converts to
an atom of the same head and arity joins it. Int-valued atoms still key by
spelling alone (`affine_syntax`'s final `intern_by` in
`crates/elab/src/omega_cert.rs`):

```text
theorem int_side(g: List<Nat> → int::Int, h: g(list::List::append(Nil, Nil)) = g(Nil) + int::OfNat(1)): False { omega }
-- stuck: atoms [g(list::List::append(Nil, Nil)), g(Nil)]
```

## Shape of a fix

The Nat side's `convertible_atom` compares at `Type::Nat`; the Int side needs
the Int carrier `Type` for `convert_term`, which `affine_syntax` does not
have — `Le`/`Lt` facts do not carry it, only an `Id` does. Resolve it once per
omega call (the reflected facts already name `int::Int`) and pass it down, or
store it with the atom table. A closed Int atom computing to a constructor
value (`OfNat(n)`, `NegSucc(n)`) would also want the numeral reader, reading
through the Int constructor to `nat_value`.

## Acceptance

- The one-liner above checks.
- The Nat-side controls' Int analogues (different values, distinct variables)
  stay two atoms.

No real Int proof has met this yet; it is the Nat fix's symmetric half.

## Log

- 2026-09-27: Done. `affine_syntax`'s fallback mirrors the Nat side: spelling lookup, then
  `int_value` (bounded whnf to an `OfNat`/`NegSucc` constructor, payload read by
  `nat_value`), then `convertible_atom` with a `Carrier::Int`, whose type is
  elaborated from `int::Int` lazily, once a pair passes the syntactic gates.
  The one-liner checks; a closed atom on each side of zero reflects as its
  constant; both controls stay two atoms (`omega_atoms_computation.rs`). Design
  note: docs/omega-measure-reduction-design.md §5.
