---
title: Legalize FunctionIR shifts against x86 masked shift counts
status: open
labels: [compiler,function-ir,x86,semantics,legalization,bitvec]
area: heather-in-heather
created: 2026-09-01
updated: 2026-10-28
---

FunctionIR shift nodes use an immediate mathematical Nat count. Logical shifts
by at least the width produce zero and arithmetic right shift fills with the
sign bit. x86-64 scalar shifts instead mask the count to six bits, so blindly
selecting `SHL/SHR/SAR r64, imm8` changes the result at counts 64 and above.

Define a legalization rule before adding the machine instruction pattern. For
counts below 64, one immediate shift is correct. For larger constant counts,
select the FunctionIR result directly—zero for left/logical-right, and a
sign-fill construction for arithmetic-right—or route through an explicit
legalized operation with a proof of equivalence. Do not weaken FunctionIR
semantics to match one target's masked-count behavior.

This issue initially owns 64-bit immediate shifts. Variable shift counts and
other widths should be recorded separately when their first concrete consumer
appears.

## Acceptance

- Immediate SHL/SHR/SAR canonical encodings, decoding, lengths, flags/frame,
  and register results are modeled for the emitted subset.
- Counts 0, 1, 63, 64, 65, and a very large compact Nat have explicit positive
  controls against FunctionIR semantics.
- No count ≥64 is compiled as though x86 did not mask it.
- A mixed shift/binary DAG checks end to end and preserves real block layout.
- The selected proof identifies legalization separately from instruction
  selection so another target can choose different rules.

## What it assumes from elsewhere

- **[[function-ir-alu-core]]** supplies logical and arithmetic shift semantics.
- **[[function-ir-x86-constants]]** supplies immediate encoding and
  variable-length block layout.

## Log

- 2026-10-28: Tracker tidy: dropped `blocked-by: [function-ir-x86-constants]`, which is closed (immediates and variable-length layout landed). The scope still stands: the verified lowering refuses the three shift nodes (`Region::lower`, `lib/native/function_ir/function_ir_lower.hthr`, `ShiftLeft(_, _, _, _) => None`), and `Asm` has no shift instruction forms yet, so the legalization rule and the SHL/SHR/SAR forms both land against the verified lowering rather than the per-function path B2 retired.
- 2026-11-05: gardener: cites a file it shares with [[function-ir-verified-lowering]] (`lib/native/function_ir/function_ir_lower.hthr`).
