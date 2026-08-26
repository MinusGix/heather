---
title: Decide which additional relation laws deserve standard-library names
status: open
labels: [stdlib,logic,semantics,proofs,design]
created: 2026-08-26
updated: 2026-08-26
---

The initial relation kit proves its core composition and inclusion laws but
deliberately stops short of a complete algebra.  Likely customers may want
converse involution, converse of composition, graph identity/composition,
framing monotonicity, and composition distributing over finite choice.

Inventory real proof sites before adding them.  Add the small laws that remove
repeated proof work, decline laws with no customer, and give every retained law
an open-input integration probe.  This issue may close with a documented
decision that the existing kit is already the right size.

## What it assumes from elsewhere

- **[[relational-semantics-refinement-kit]]** owns the existing algebra and is
  the baseline against which demand should be measured.
