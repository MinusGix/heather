---
title: Separate Cauchy, conditional, and order completeness
status: open
labels: [stdlib,mathematics,reals,analysis,design]
created: 2026-09-02
updated: 2026-09-02
---

Design completeness capabilities only after writing their quantified data
precisely. Compare regular/Cauchy completeness with explicit moduli,
sequential completeness, least-upper-bound or conditional completeness, and
located/order completeness. Record exactly where countable choice,
extensionality, or classical principles relate them.

These should be orthogonal capabilities over ordered-field-like structures,
not one oversized `CompleteReal` class. Each proposed class needs a theorem
that consumes it and one presentation expected not to inhabit it
constructively.

## What it assumes from elsewhere

- **[[constructive-ordered-field-interface]]** owns the common scalar laws.
- **[[axiom-provenance]]** owns tracking imported principles.

## Log

- 2026-09-02: Filed to keep the Cauchy/Dedekind split visible in interfaces.
