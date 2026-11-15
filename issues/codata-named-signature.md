---
title: Name each codata signature as generated definitions
status: closed
labels: [codata,coinduction,elaborator,performance]
area: interaction-trees
milestone: [it-coinductive]
created: 2026-10-22
updated: 2026-10-22
---

Every occurrence of a codata type spelled its whole `M` signature inline, and
a declaration over another codata type (`Bisim` over `CoTree`) nested one
inline signature in the next. Proofs over `Bisim` paid for the product of
the signatures' sizes at every node, in the elaborator and in the kernel
term.

Done in `docs/inductives/codata-named-signature-design.md`: `D#mshape`, `D#mpos` and
`D#mnext` name the signature's parts over the `tycode_fn` telescope, the
structural readers unfold the references, the instance matcher learned `M`
(so inductives with codata fields get their `tycode_fn` reference), and the
three codata entry points emit the kernel's checked spelling.

## Log

- 2026-10-22: Implemented on branch claude/project-thread-lozmdm. `Bisim::refl` and `Bisim::sym` over `CoTree` dropped by more than an order of magnitude; the codata tests are unchanged and pass.
