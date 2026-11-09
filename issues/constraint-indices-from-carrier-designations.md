---
title: A constraint at a nominal carrier restates every index its designations already name
status: open
labels: [notation,traits,elaboration,ergonomics]
area: language
milestone: [math-classes]
created: 2026-11-09
updated: 2026-11-09
---

Split from [[section-symbols-capture-other-carriers]], whose first half
landed. The transfer sections in lib/std/num/float/float_real.hthr and
round_real.hthr take the homomorphism as

```heather
hom: OrderedRingHom<Rat, K>(map, Rat::Same, Rat::Lt, Rat::Le, Rat::add, Rat::mul,
    Rat::neg, 0, 1, ≈, <, <=, +, *, K.inv, K.unit, K.multiplicative.unit)
```

where every `Rat` index is what `Rat`'s designations already say (`≈`, `<`,
`<=`, `+`, `*` at `Rat`), and every `K` index is the section binder's.

## Direction

Let a class's indices that a carrier designates be left to the designation
rung in a constraint, so the header is `OrderedRingHom<Rat, K>(map)`: the
`Rat` side from `Rat`'s designations (operators-onto-classes-design §5(a),
the call-site fill, at a declaration's own constraint), the `K` side from
the section's binder. [[constraint-index-binder-introduction]] and
[[class-default-operators]] own the surface; this issue asks only that the
side at a nominal carrier not be restated.

## Acceptance

- The two sections' headers read `OrderedRingHom<Rat, K>(map)` and the
  modules check unchanged (identical terms: the kernel verdicts replay).
- A carrier with no designation for an index is refused naming the carrier
  and the index.

## Also carried from the parent

Diagnostics inside such a section still spell a `Rat` relation as
`Rat::Le(a, b)`: display.rs keeps rung 1's block on any symbol a binder
installed. It may lift it where the resolver now would read the symbol back
(an operand at a nominal carrier other than the binder's, not numerals
alone), which display can tell from the callee's declared operand carrier.

## Log

- 2026-11-09: Filed as the residue of [[section-symbols-capture-other-carriers]].
