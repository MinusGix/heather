---
title: omega keys atoms by spelling: atoms equal by computation stay separate
status: closed
labels: [omega,proofs,elaboration,ergonomics]
created: 2026-09-27
updated: 2026-09-27
---

`omega` keys atoms by their spelling, so two atoms that are equal by
computation stay separate variables, and a closed atom that computes to a
numeral stays opaque:

```text
theorem appended(f: List<Nat> → Nat, h: f(list::List::append(Nil, Nil)) = f(Nil) + f(Nil)): f(Nil) = 0 { omega }
-- stuck: atoms [f(list::List::append(Nil, Nil)), f(Nil)]
theorem closed_bit(x: Nat, h: Nat::of_bit(True) + x = 0): False { omega }
-- stuck: atoms [nat::Nat::of_bit(True), x]
```

Both come from writing `lib/elf64_read_loop.hthr`'s read-until-EOF proofs
([[native-read-until-eof]], 2026-09-27). There, `spec(Nil ++ Nil)`,
`spec(eof_input(Nil))` and `spec(Nil)` were three atoms, and so were
`of_bit(True)` in `test_self_zero` and `1`. Each needed an annotated
restatement before `omega` would see the fact (`let c: (carry + spec(Nil) =
total) = counted;`). A proof author reaches for `omega` precisely where the
arithmetic is obvious, so this is a trap even on small goals.

## Shape of a fix

Normalise an atom's arguments before keying it: a cheap whnf of each closed
subterm (`of_bit(True)` ↦ `1`, `append(Nil, Nil)` ↦ `Nil`), or key atoms up to
conversion with a bounded check against the atoms already in the table. The
first is enough for both reproducers above, and it stays inside the
reflection. The certificate still spells the atom as it met it, so the
kernel's conversion does the same work it does today.

Cost to watch: atoms are reflected per hypothesis, so normalising every
argument must stay cheap. Bound it (whnf only, and only on closed or
constructor-headed arguments).

## Acceptance

- Both one-liners above check.
- A negative control: `f(Cons(0, Nil))` and `f(Nil)` stay distinct atoms.

## Log

- 2026-09-27: Done. Nat atoms whose spelling is new are (1) evaluated under
  `ATOM_COMPUTATION_STEPS` by a new kernel reader `eval::nat_value` (only for
  global heads) and become a constant when they compute to a numeral, then (2)
  after the measure-reduction fallback, compared by bounded conversion with the
  table's atoms of the same head and arity, skipping pairs that differ only in
  distinct variables. Both one-liners check; `f(Cons(0, Nil))` against
  `f(Nil)` stays two atoms (`crates/elab/tests/omega_atoms_computation.rs`).
  `lib/elf64_read_loop.hthr` drops both restatements. Design note:
  docs/omega-measure-reduction-design.md §5. Int-valued atoms are residue:
  [[omega-int-atoms-up-to-computation]].
