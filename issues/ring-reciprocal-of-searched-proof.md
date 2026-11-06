---
title: Read a reciprocal's fact in ring when its apartness was searched through a rule
status: open
labels: [tactics,mathematics]
area: tactics
milestone: [tac-arith]
created: 2026-11-06
updated: 2026-11-06
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
