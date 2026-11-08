---
title: A section's operator symbols capture every carrier, so a second carrier is written prefix
status: open
labels: [notation,traits,elaboration,ergonomics]
area: language
milestone: [math-classes]
created: 2026-11-08
updated: 2026-11-08
---

A constraint binder that names a symbol (`section<K: OrderedField(≈, <, <=,
+, *)>`) installs it as rung 1 of the operator ladder, which "fires without
looking at any type" (docs/operators-onto-classes-design.md §4). Inside that
section, `+`, `<=` and numerals mean `K`'s even when the operands are at
another carrier:

```heather
section<K: OrderedField(≈, <, <=, +, *)> {
theorem s_two(x: K, a, b: Rat, h: a <= b): a + 0 <= b { … }
// no instance for `Numeral<the expected type>` … candidate rat::Rat::Numeral
//   rejected: built, but not of the goal type
}
```

So every proof that relates a carrier to `K` writes the other carrier's
arithmetic by name. In lib/std/num/float/float_real.hthr and round_real.hthr
(the transfer from `Rat` to any ordered field through a homomorphism `map`),
statements read

```heather
theorem Rat::affine_up(x: K, lo, R, a, b: Rat, a_nn: Rat::Le(0, a), l: map(lo) <= x,
    at: Rat::Le(R, Rat::add(Rat::mul(a, lo), b))): map(R) <= map(a) * x + map(b)
```

where `0 <= a` and `R <= a * lo + b` were meant: 66 lines of `Rat::Le(`,
`Rat::add(`, `Rat::mul(` … in those two files alone. The section header
itself spells every index of both carriers:
`OrderedRingHom<Rat, K>(map, Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul,
Rat::neg, 0, 1, ≈, <, <=, +, *, K.inv, K.unit, K.multiplicative.unit)`. The
refusal above also names a type that nobody wrote ("the expected type").

## Direction

Make rung 1 carrier-aware once the operand's type is known: a binder's
symbol applies to operands at the binder's carrier (or at a still-unknown
type, as now); an operand with a head of its own goes to rung 2, the
designation at that head. That keeps generic code as it is (its operands
are at `K`) and lets `a + 0 <= b` at `Rat` mean `Rat`'s. The left-spine
probe of §4.1 already computes the operand's type before the head is chosen.

Second, smaller: let a class's indices that a carrier designates be left
to the designation rung in a constraint, so the homomorphism above is
`OrderedRingHom<Rat, K>(map)` with `K`'s indices from the section's binder
([[constraint-index-binder-introduction]], [[class-default-operators]] own
the surface; this issue only asks that the Rat side not be restated).

## Acceptance

- `s_two` checks with `a + 0 <= b` at `Rat` inside the section, and
  `Rat::affine_up`'s statement is written with operators.
- Control: inside the section, `x + y` at `K` still resolves to the binder,
  and an operand at a carrier with no designation for the symbol is refused
  naming that carrier, not "the expected type".

Related: [[operation-indexed-classes]]; docs/stdlib-math-awkwardness-survey.md §6.
