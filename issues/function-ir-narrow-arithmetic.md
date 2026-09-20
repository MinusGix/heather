---
title: Certify modular narrow arithmetic and signed comparisons
status: open
labels: [compiler,function-ir,x86]
created: 2026-09-20
updated: 2026-09-20
---

Shared x86 lowering represents widths 0–64 with zero-extended register values.
Constants, copies, bitwise operations, and unsigned comparisons can preserve
that invariant using ordinary word instructions. Narrow addition/subtraction
and signed comparisons still deliberately decline.

Add general selection and certificate rules for modular narrow arithmetic
(masking or equivalent normalization after word operations), and an explicit
signed representation/comparison rule. Reuse the existing FunctionIR nodes,
allocator, machine model, and per-value placement proofs. Cover overflow,
underflow, sign boundaries, width zero policy, and live mixed-width values.
Reject proofs that substitute full-word arithmetic for modular narrow results.

This extends [[native-bounded-loop-certificates]] and the shared backend;
it is independent of application-specific loop bodies and of
[[function-ir-shared-multi-result-dag]].
