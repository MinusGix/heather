---
title: Lower FunctionIR's pure regions by a Heather function proved correct once
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
blocked-by: [native-one-wp]
created: 2026-10-21
updated: 2026-10-21
---

Round S4 of `docs/native-program-logic-design.md` (§3.2, §9): lower
FunctionIR's pure regions to x86 by a Heather function whose correctness is
one theorem, replacing the per-function certificate path (Rust lowering,
`heather_emit`, the structured and control-block certificates).

## Scope

- `lower : CheckedRegion → Prog` (or code with a contract) in Heather, with
  register placement as part of it or as a checked input.
- One theorem: the lowered code computes the region's meaning, as a
  `Proved` contract (outputs in their registers, scratch named, the rest
  kept).
- The `examples/x86-native` pure examples (branches, calls, composition,
  sharing, stack) built through it, after which burn B2 can start.

## What it assumes from elsewhere

- **[[native-one-wp]]** owns `Proved` and `Wp`.
- **[[in-language-certificate-emission]]** and
  **[[generators-in-the-language]]** own how a Heather metaprogram is run by
  the compiler; this issue assumes only that `lower` can be evaluated.
