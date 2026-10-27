---
title: Taylor models: polynomial enclosures with an interval remainder
status: open
labels: [mathematics,reals,intervals]
area: mathematics
created: 2026-10-27
updated: 2026-10-27
---

`docs/analysis-foundations-design.md` §6.1: Taylor models (a polynomial in a
variable on an interval domain plus an interval remainder) as the uniform
reading of a certified expansion, and as the next step for the interval
checker after `Interval` (the order-0 Taylor model).

Scope:

- a Taylor model record over `Dyadic`/`Rat` coefficients with an `Interval`
  remainder on a domain, containment at `CReal` (`HasReal` analogue);
- arithmetic: sum, truncated product with the dropped terms bounded into the
  remainder, composition with the elementary functions' expansions;
- a probe where intervals lose and Taylor models do not (the dependency
  problem: `x - x`, `x·(1 - x)` over a range).

## What it assumes from elsewhere
- **[[certified-expansions]]**: the expansion record and its operations.
- **[[dyadic-interval-enclosures]]** (closed) and **[[interval-creal-enclosures]]**:
  the interval layer and its checker.
