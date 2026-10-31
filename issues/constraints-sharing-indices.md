---
title: Two constraints over the same operations, without a combined class
status: open
labels: [traits,frontend,design]
area: language
created: 2026-10-30
updated: 2026-10-30
---

A declaration cannot say `A: OrderedField(≈, <, <=, +, *)` and
`A: CommRingOfInt(≈, +, *)` together: each constraint installs `≈`, `+` and
`*` again, and the second is refused (docs/linarith-design.md). The library
has answered with combined classes that add nothing but the pairing:
`OrderedFieldOfInt` (`linarith`'s certificates), and the
`OrderedFieldOfRat` that the [[interval-containment-once-over-ordered-field]]
assessment prototyped and then dropped. Minus (2026-10-30): the combined
classes are the wrong pattern; two constraints over the same operations
should work properly.

What "properly" has to mean:

- A later constraint's slots can *link* to indices an earlier one declared
  (the bare-name linked reference [[constraint-index-binder-introduction]]
  preserves), so both dictionaries are over one `≈`, one `+`, one `*`, and
  notation is installed once.
- Two dictionaries can reach one ancestor (`OrderedField` and
  `CommRingOfInt` both reach `CommRing`). Field reads through either must
  agree, or resolution must pick one deterministically. The
  ambiguity rule in [[requires-placement-syntax]] and
  [[class-default-operators]]' collision rule are the neighbours.
- A call at a concrete carrier resolves both from instances, as one
  constraint does today.

Not every pairing needs this: an embedding is better passed as a morphism
value ([[casting-standard]] §5.6) than as a capability of the carrier. But
`OrderedFieldOfInt` is a capability pairing, and it is the case to retire
first.

## Log

- 2026-10-31: Probed. Linking is easy and works where the two classes share
  no ancestor: in `expand_constraints` (crates/elab/src/traits.rs), a symbol
  slot whose symbol an earlier constraint installed at the same carrier
  pushes a reference to that constraint's index binder instead of a new
  binder, and `<A: OrderedField(≈, <, <=, +, *) + CommRingOfInt(≈, +, *)>`
  then checks a lemma that reads `A.of_int` and `A.rel_refl`, and a `Rat`
  call resolves both dictionaries. It breaks at the shared ancestor: the two
  dictionaries are two locals, so `CommRing`'s fields reached through each
  are different terms. `A.unit < A.of_int(1)` from `A.zero_lt_one`
  (`OrderedField`'s, over its own `unit`) and `A.of_int_one`
  (`CommRingOfInt`'s, over its own `multiplicative.unit`) is refused as
  `<(#constraint0.unit, …)` against `<(#constraint1.unit, …)`; `A.unit`
  written in the body resolves through the innermost dictionary. No
  deterministic choice fixes that: `linarith`'s lemmas mix laws only one
  side has, each stated over its own copy of the ancestor. So "properly"
  needs one dictionary in which the ancestor occurs once, which is what
  class declarations already do for a diamond (`OrderedField`'s `GroupRel`
  through both parents). The shape that follows: linked constraints at one
  carrier become one binder of a synthesized combined class (extends both,
  no fields of its own, named by its parents so two declarations writing
  the same pair share it), and at a concrete carrier its goal is assembled
  from the parents' instances, each merged field from the first parent that
  declares it, as an empty-bodied `instance OrderedFieldOfInt<Rat>(…) {}`
  is assembled today. The linking patch alone is not landed: it would turn
  this refusal into the confusing mismatch above.
