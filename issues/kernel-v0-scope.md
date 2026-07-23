---
title: Pin down the DeLaM fragment for kernel v0
status: open
labels: [kernel, delam]
created: 2026-07-22
updated: 2026-07-22
---

Decide exactly which fragment of DeLaM (docs/delam/) the first Rust kernel
implements: layer structure, box/contextual types, recursion over code at the
meta layer, universe setup, and conversion checking (NbE, following the
decidability development). Mirror the judgments and structure of the
in-progress Coq formalization so the Rust code is recognizably "the same
rules" and divergences are auditable.

Deliberately out of scope for v0: coinduction (see [[effects-direction]]),
typeclass resolution, any compiler machinery.

First concrete artifact: the term/judgment representation in
`crates/kernel`, plus a checker that can verify small hand-elaborated terms.

## Log

- 2026-07-22: Read ch.04 fully + 05 (subst ops), 06, 08. Scope pinned in crates/kernel/DESIGN.md; docs/delam/README.md warns 01-03 is the simplified warm-up system. Representation landed: layer.rs, level.rs (count/adjust normalization, tested), term.rs (full ch.04 syntax, de Bruijn, 3 namespaces). Conversion will be ch.06 WHNF-reduction style, NOT NbE.
