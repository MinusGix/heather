---
title: A constraint at a nominal carrier restates every index its designations already name
status: closed
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

## Log

- 2026-11-09: Filed as the residue of [[section-symbols-capture-other-carriers]].
- 2026-11-09: First step: a bare symbol a section's binder named now resolves
  at the slot's own carrier when the expected type's first domain is a
  nominal one (`binder_declines_operands`, bare direction), so the headers
  read `OrderedRingHom<Rat, K>(map, ≈, <, <=, +, *, Rat::neg, 0, 1, ≈, <,
  <=, +, *, K.inv, K.unit, K.multiplicative.unit)` (interval, float_real,
  round_real, cast_tests; kernel verdicts replayed, so the terms are
  identical). `-` has no bare prefix form, so `Rat::neg` stays. Leaving the
  indices out altogether is open: proposed as index defaults
  (`same_a: A → A → Type := ≈`, an omitted trailing index elaborated at the
  use site), which is named-arguments-design §9's staged binder default
  applied to a type's indices, with its free symbols resolved at the use
  site rather than the declaration's.
- 2026-11-09: Index defaults landed (Minus picked them over stopping at bare
  symbols). A `record`'s trailing value parameters may end `:= e`
  (parser `valparam_list(_, defaults)`; `Inductive::valparam_defaults`, in
  the module image, format bumped); `valparam_args_after` fills an omitted
  suffix by checking the default at the slot's instantiated type under the
  use site's symbols, stored η-short (`index_default_short`) so the
  structural record's indices stay learnable (`?neg_b := K.inv`).
  `OrderedRingHom`'s indices default to `≈ < <= + *`, `λ x => -x`, `0`,
  `1`, and the four transfer headers are `OrderedRingHom<Rat, K>(map)`;
  `ring`/`mono`/`linarith` through the local morphism unchanged
  (cast_tests). Docs: surface-value-parameters §6.5. The display residue
  moved to [[section-display-other-carrier-symbols]].

