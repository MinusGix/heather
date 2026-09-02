---
title: Design a constructive ordered-field interface
status: open
labels: [stdlib,mathematics,reals,algebra,order]
created: 2026-09-02
updated: 2026-09-02
---

Identify the abstract ordered-field structure actually shared by rationals and
constructive real presentations. Treat setoid equality, strict order,
non-strict order, apartness, positivity, inverse-on-apart elements, and the
Archimedean property explicitly; do not smuggle classical trichotomy or
decidable equality into the name.

Probe whether locatedness belongs in the base interface or in a separate
capability. The acceptance should state useful generic interval/absolute-value
theorems at the weakest demonstrated layers.

## What it assumes from elsewhere

- **[[ordered-algebra-api]]** owns order/algebra compatibility.
- **[[apartness-structures]]** owns apartness laws.
- **[[positive-naturals-and-rationals]]** supplies the first carrier.

## Log

- 2026-09-02: Filed to provide shared real-number mathematics without claiming
  that every presentation is definitionally or constructively identical.
