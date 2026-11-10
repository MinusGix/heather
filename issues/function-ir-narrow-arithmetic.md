---
title: Certify modular narrow arithmetic and signed comparisons
status: open
labels: [compiler,function-ir,x86]
area: heather-in-heather
created: 2026-09-20
updated: 2026-11-10
milestone: [crypto-hash]
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
- 2026-10-25: Read against `docs/multi-width-bitvector-survey.md` §3 (Bhat et al., OOPSLA 2026). The verified lowering now refuses every width but 64 and 1 (`word_only` in `function_ir_lower.hthr`). The shared lowering that published `tr`'s narrow add/sub was retired in B2, but its laws remain (`BitVec::add_zero_extend_mask`, `sub_zero_extend_mask`). Generalising `Kind` from Word/Bit to "width w, held as `values(w, id).zero_extend(64 - w) = word`" is the paper's compatibility relation (Definition 4.1) at o = 64. Its Table 2 is the per-node rule list: constants, Move, and/or/xor, unsigned less-than and equal are mask-free on zero-extended inputs, while add/sub/neg/shl mask after (a MOV imm64 for w >= 32). For the open signed comparison, use the sign flip `slt_w(a, b) = ult(a xor 2^(w-1), b xor 2^(w-1))`: an XOR-immediate per operand, then the existing CMP/SETB. Brute-force checked at widths 1-6. Do not port the paper's Table 2 slt row as printed: it is wrong when both operands are negative (survey §6).
- 2026-11-05: gardener: cites a file it shares with [[lrat-certified-bitvector-decision]] (`docs/multi-width-bitvector-survey.md`).
- 2026-11-10: Probe, 2026-11-10 (`native-roadmap/sha_native.hthr` in the project folder):
  SHA-256's Σ1 and T1 over `BitVec(32)` reflect to `rt` and their `agrees`
  theorems check, then `compile-x86` refuses both with "the verified lowering
  refused this program with the planner's placement" (`word_only` in
  `function_ir_lower.hthr` admits widths 64 and 1; `Resize` lowers to `None`).
  The same Σ0 at width 64 certifies. So SHA-256 is this issue's first real
  consumer ([[sha2-compress-native]]), and it wants the zero-extension
  invariant kept by 32-bit instruction forms rather than by masks after
  64-bit ones ([[x86-narrow-and-rotate-forms]]): a mask per add would
  double the round function.
