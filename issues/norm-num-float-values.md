---
title: Decide closed facts about Float(F) values in norm_num
status: open
labels: [tactics,arith,float]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

`norm_num` ([[numeral-normalisation]], docs/numeral-normalisation-design.md)
decides `≈`, `<` and `<=` at `Finite(F)`, through `Finite::val`. The float
literals denote `Float(F)` values (`b64(0.1)`), and `Float(F)` has only
structural `=` and the named IEEE comparisons, so a client stating a fact
about two literals, or about `x.add(y)`, reaches neither.

Wanted: `norm_num` reads `Float(F)` goals too.

- `=` at `Float(F)` by a `Bool` equality on the three parts (sign,
  magnitude, biased exponent) and on the specials, proved sound once, so a
  closed float equation is a verdict, never a `refl` over the record;
- the quiet comparisons and `totalOrder` on `Float(F)`, as verdicts;
- `Finite` facts about a `Float` known to be finite (`x.finite() = Some(f)`),
  read through `Float::finite`.

## What it assumes from elsewhere
- **[[numeral-normalisation]]**: the verdict route and the tactic's
  carrier dispatch, which this extends by one carrier.
