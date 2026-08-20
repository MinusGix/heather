---
title: "Research a constructive core and classical interface for real numbers"
status: open
labels: [stdlib,mathematics,research,design]
created: 2026-08-20
updated: 2026-08-20
---

Choose the foundational representation and library boundary for real numbers
before accumulating analysis APIs. The central question is not simply
“constructive or classical”: it is which facts compute, which equalities are
quotients or setoids, which completeness principles require choice or excluded
middle, and whether classical reasoning can be isolated above a useful
constructive base.

The default direction to investigate is a constructive core with an optional
classical interface, but it must earn that position against concrete Heather
constraints. Compare at least regular/Cauchy reals and Dedekind/located-cut
presentations; account for equality, order, apartness, completeness,
computation, extraction, and the current quotient/setoid story. A beautiful
definition that makes ordinary algebra or limits unusable is not a core basis.

The output is a design note and small executable probes, not a full real
analysis library.

## Acceptance

- Compare candidate constructive representations and one deliberately
  classical presentation against Heather's current type theory.
- State the equality story for each: definitional equality, propositional
  equality, setoid equivalence, or a future quotient requirement.
- Implement small probes for arithmetic, order/apartness, rational embedding,
  and at least one convergence/completeness statement.
- Inventory exactly where excluded middle, choice, proof irrelevance,
  extensionality, or quotient elimination would enter.
- Recommend a layering: core representation, constructive analysis API, and
  explicitly imported classical principles—or explain why that split fails.
- Connect the decision to the intended semantics of finite sums, infinite
  series, measures, and integrals in [[big-operator-semantics]].

## What it assumes from elsewhere

- **[[setoid-auto-lifting]]** owns automation for transporting operations and
  proofs across setoid equivalence. Assumed here: setoids are available as a
  candidate technique, not already selected as the real-number representation.
- **[[axiom-provenance]]** owns explicit assumption declarations and transitive
  dependency reporting. Assumed here: competing real-number foundations can
  be compared by where classical principles enter, not only by a flat axiom
  list at the final theorem.

## Log

- 2026-08-20: Filed as research/design. Constructive foundations are the
  preference to test; “core” remains a usability and dependency decision, not
  an ideological label.
