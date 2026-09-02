---
title: Probe regular Cauchy reals constructively
status: open
labels: [stdlib,mathematics,reals,analysis,setoids]
created: 2026-09-02
updated: 2026-09-02
---

Implement a small executable presentation of regular Cauchy reals over
rationals, with explicit approximation rate or modulus and extensional setoid
equality. Probe rational embedding, arithmetic, apartness/order, and one
diagonal completeness construction.

The output is a representation/design probe, not a full analysis library.
Measure proof ergonomics and computation, and list every use of choice,
extensionality, proof irrelevance, or classical reasoning (ideally none in the
core).

## What it assumes from elsewhere

- **[[positive-naturals-and-rationals]]** owns rational arithmetic.
- **[[real-completeness-interfaces]]** owns the abstract capability names.

## Log

- 2026-09-02: Split from [[real-number-foundation]] for a concrete
  computational presentation.
