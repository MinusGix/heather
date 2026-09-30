---
title: Fuse FunctionIR comparisons into direct x86 conditional branches
status: closed
labels: [compiler,function-ir,x86,optimization,control-flow]
blocked-by: [x86-64-conditional-branch-layout]
created: 2026-09-01
updated: 2026-09-29
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

## Log

- 2026-09-29: Designed as slice F of docs/structured-lowering-code-size-design.md (§2): a condition-code jcc family and CodeBranch over BranchTest::Compare, with the CMP inside the branch so that no flag crosses an artifact boundary. The materialised rule stays wherever the bit has another consumer.
- 2026-09-29: Landed (docs/structured-lowering-code-size-design.md §2.4). A Sequence whose prefix ends in a 64-bit comparison that only the following Conditional reads, with one operand computed by the prefix, lowers to FusedSequence: the operand DAG, then CodeBranch(Compare(l, r, B|L)), which is CMP and a Jcc on its flags. The certificate ties branch_skips to the comparison through unsigned_compare_skips / signed_compare_skips. CMP sits inside the branch, so no flag is live across an artifact boundary. Every other shape keeps the materialised rule. Bytes: field_low 1,911 → 1,534, field_high 2,792 → 2,225. Tests: interpreter (unsigned from source, signed hand-built, at the edges), certificates with wrong-code and swapped-operand mutants refused, and unsigned_threshold natively against C.
