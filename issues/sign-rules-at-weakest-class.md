---
title: State the sign rules at the weakest class that proves them (use what you need)
status: open
labels: [mathematics,traits,performance]
area: mathematics
milestone: [math-classes]
created: 2026-11-06
updated: 2026-11-06
---

The sign rules that let `/` and `⁻¹` find their apartness proof over a class
carrier (lib/std/algebra/field_division.hthr: `positive_add`, `nonneg_mul`,
`positive_neg`, `nonneg_mul_self`, …) are all stated in
`section<A: OrderedField(≈, <, <=, +, *)>`, although only the reciprocal rules
need a field. `positive_add` is a fact about an ordered additive monoid,
`positive_mul` about an ordered semiring, `positive_neg` about an ordered ring.
Each rule should sit at the weakest class whose laws prove it
(docs/division-design.md §6; the ordered layers already name theorems by
their weakest class), so a client uses only what it needs.

## Why they were not

They were, at first. Each application of a weaker-class rule at an
`OrderedField` section paid for an upcast: the rule's dictionary premise
(`OrderedSemiring(…)`) was answered by assembling the parent record from the
section's field dictionary and kernel-checking it, at every use. That cost
about 20x a field-level rule.

The open-derivation round (resolve.rs `record_open`/`open_hit`, 2026-11-06)
removes most of that. An upcast or merged-class assembly found at a class
carrier is minted between items as one global over the context prefix it lives
in, and every later item with that prefix reads it as an application. What is
left:

- The first item of each section prefix still assembles the upcast inline.
- More rules per relation key. `PositiveBy` gets a rule per class, and each
  is a trial. `rule_clashes` only rejects rules whose operation binders cannot
  match.

So: re-measure a weaker-class `positive_add` against the field-level one with
`scripts/perf ab --source-patch` first, then move the rules.

## What it would give

- **Generic positivity below fields.** `PositiveBy(<, <=, K.unit, a + b)` by
  `:= infer` in any ordered semiring section, not only fields. The same goes
  for every other sign side condition: `pow` laws, `sqrt`/`log` preconditions
  over any ordered ring, a divisibility side goal over a semiring.
- **One rule set for every carrier.** `Nat`, `Int` and `Dyadic` have ordered
  semiring/ring instances, so they would get the generic rules through their
  instances. `Rat` and `CReal` keep their own copies today
  (issues/carrier-division-through-class.md). Rules at the weakest class are
  what lets those copies go: a carrier then needs only its instance.
- **Laws reusable where they hold.** `positive_mul_neg` and `nonneg_mul_self`
  are ring facts that today a client of `OrderedRing` cannot cite.
- **The cost lesson generalises.** A library written against weak classes and
  used at strong ones is exactly the case open derivations make cheap, so this
  is also their test at scale.

## Steps

1. Measure, as above.
2. Move each sign rule to its weakest class (`OrderedAddMonoid`,
   `OrderedSemiring`, `OrderedRing`), leaving the reciprocal and apartness
   rules (`positive_inv`, `invertible_*`) at `OrderedField`.
3. Probes in lib/_tests at an `OrderedRing` section, at `Int` through its
   instance, and at the field, to show that the field search is unchanged.
