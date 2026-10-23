---
title: Certify modular narrow arithmetic and signed comparisons
status: open
labels: [compiler,function-ir,x86]
area: heather-in-heather
created: 2026-09-20
updated: 2026-09-30
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

## Log

- 2026-09-30: 2026-09-30: Add/subtract half landed for [[native-tr]] (docs/native-tr-design.md §4.2): the word's operation, then MOV scratch, 2^w-1 and AND; law BitVec::add_zero_extend_mask / sub_zero_extend_mask in lib/std/bitvec/bitvec.hthr, structural in the width. Tests: execution at widths 0-63 at the carry/borrow edges, certificates for copied/constant/reversed/width-0/chained forms, an unmasked-sum negative control. upcase and ROT13 publish at tr's registers (117 and 353 bytes; about 1 s and 4 s to check at width one). Still open here: narrow signed comparisons.
