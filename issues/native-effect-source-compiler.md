---
title: An effectful source denoting Linux trees, and its compiler proved correct once
status: open
labels: [native,x86,ir,proofs,design]
area: heather-in-heather
blocked-by: [native-loop-rule, function-ir-verified-lowering]
created: 2026-10-21
updated: 2026-10-21
milestone: [hih-pl-source]
---

Round S3 of `docs/native-program-logic-design.md` (§7): an effectful source
whose programs denote Linux trees, its compiler to `Prog` written in
Heather, and the compiler's correctness theorem proved once.

## Scope

- Decide the source: FunctionIR grown with effect nodes, or a small
  tree-shaped layer whose leaves are FunctionIR regions (the design's lean).
- `denote` (compositional: sequencing is `bind`, loops are `iter`) and
  `compile`, with the register and frame conventions stated once as the
  invariant between constructs.
- One lemma per construct, over abstract inputs, proved with `Wp` and
  `loop_at`; the theorem by induction on the source: `Sim` at `denote(p)` of
  the assembled `compile(p)`.
- Whether the read's buffer size is fixed by the source or abstracted
  (design §10, question 1).

## What it assumes from elsewhere

- **[[native-one-wp]]**, **[[native-loop-rule]]** own the target-side tools.
- **[[function-ir-verified-lowering]]** owns pure regions' code; assumed
  here only as `Proved` items with the lowering's theorem as contract.
- **[[effects-direction]]** owns the surface that elaborates to this source.

## Log

- 2026-10-21: Minus's answers (design §10): the surface is uniqueness threading that denotes trees (item 5); the source's shape stays open, with the input for this round in item 6 (external effects in the tree layer, internal effects as FunctionIR state edges; decide by writing `tr` both ways first). Where loops live is decided with it: [[function-ir-lowering-loops]]. Before B2, also [[function-ir-source-denotation-after-b2]].
