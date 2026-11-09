---
title: Read a reciprocal's fact in ring when its apartness was searched through a rule
status: closed
labels: [tactics,mathematics]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-08
---

`ring` reads a reciprocal `x⁻¹` with its fact `x⁻¹ * x ≈ 1`, written as
`<inv>_mul(x, h := <h>)` from the spelled proof (`Reifier::reciprocal_fact`,
crates/elab/src/ring.rs). When the proof was found by the search through a rule
(a product's apartness, `Rat::apart_mul`, `OrderedField::invertible_mul`) the
fact is not read, and the reciprocal is a plain atom:

```heather
// refused: differs by `Rat::inv(Rat::mul(x, y)) * x - Rat::inv(y)`
theorem t(x, y: Rat, hx: Rat::Lt(0, x), hy: Rat::Lt(0, y)): (x * y)⁻¹ * x ≈ y⁻¹ { ring }
```

Same in a section over `OrderedField`. A reciprocal of a local (`x⁻¹` at
`0 < x`) is read. Likely the searched proof term does not spell back to source
(implicit arguments of the rule), so the fact's elaboration fails silently.
A fix could elaborate the fact at the proof term itself instead of its
spelling, or re-search the apartness at the fact.

## Log

- 2026-11-08: Closed by the class-carrier-arithmetic-surface round. At
  `Rat` the example already checked on master
  (83c825d). In a section over `OrderedField` it was refused: the fact's
  arguments spelled through the section's hidden binders (`#op+@0_3`,
  `#constraint0`), which no source parses. `reciprocal_fact` now binds an
  argument with no source spelling to an alias at its kernel-inferred type
  and names the carrier, and `quotient` builds a class quotient's
  reciprocal from the quotient's own arguments. Probe:
  `ring_searched_product_reciprocal` in field_division_tests.
