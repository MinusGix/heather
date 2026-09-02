---
title: Formalize lower reals as one-sided ordered objects
status: open
labels: [stdlib,mathematics,reals,domain-theory,order]
created: 2026-09-02
updated: 2026-09-02
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
