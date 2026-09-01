---
title: Fuse FunctionIR comparisons into direct x86 conditional branches
status: open
labels: [compiler,function-ir,x86,optimization,control-flow]
blocked-by: [x86-64-conditional-branch-layout]
created: 2026-09-01
updated: 2026-09-01
---

The compositional lowering materializes a FunctionIR comparison as a canonical
zero-extended bit and subsequently tests that register before branching. That
is an important reference implementation, but x86 can normally consume the
flags from the comparison directly.

Prove a fused lowering such as `CMP` followed by `JB` for unsigned less-than,
while retaining the same FunctionIR semantics in which the comparison value
genuinely exists and feeds a `Conditional`.

## Acceptance

- Prove the fused flag-consuming branch refines the same `Sequence` and
  `Conditional` denotation as the materialized reference lowering.
- Cover both taken and untaken paths and the common join.
- State flag liveness/clobber assumptions explicitly.
- Compare linked bytes and instruction counts against the materialized rule.
- Keep the materialized rule available as a compositional fallback.
