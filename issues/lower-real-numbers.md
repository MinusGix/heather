---
title: Formalize lower reals as one-sided ordered objects
status: open
labels: [stdlib,mathematics,reals,domain-theory,order]
area: mathematics
milestone: [math-reals]
created: 2026-09-02
updated: 2026-11-10
---

Develop lower reals without forcing them into the ordered-field interface.
Choose a precise variant (bounded/unbounded, nonnegative/extended as needed)
and formalize lower cuts, roundedness, directed approximation, order, and the
algebra genuinely supported by that variant.

Use lower-semicontinuous quantities, suprema, or integration-facing examples
as forcing customers. State maps to and from located/Dedekind reals only where
the required information exists.

## What it assumes from elsewhere

- **[[relation-property-structures]]** owns generic relation laws.
- **[[big-operator-semantics]]** owns the eventual sums/measures/integrals
  connection.

## Log

- 2026-09-02: Filed as a peer real-like construction, deliberately not another
  inhabitant of a single `Real` class.
- 2026-11-10: The localic line's machinery (`Cover`, `Cover::hom`, `FormalPoint`, docs/library/localic-reals-design.md §7) presents the lower reals with lower ends only; a candidate construction for this issue, and where valuations on locales take values.
