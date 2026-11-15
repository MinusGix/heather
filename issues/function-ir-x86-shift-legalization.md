---
title: Legalize FunctionIR shifts against x86 masked shift counts
status: closed
labels: [compiler,function-ir,x86,semantics,legalization,bitvec]
area: heather-in-heather
created: 2026-09-01
updated: 2026-11-08
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
- 2026-11-08: Done (i64 round 3, docs/native/runtime-fn-setups-design.md §16.13): `ShiftOp::legalize` (counts up to 63 are themselves; SHL/SHR past are zero, SAR is SAR by 63; `legalize_sound`) apart from `File::select_shift`, which selects chains of `SHL/SHR/SAR r64, 1` (`Instruction::ShiftOne`, REX.W D1 /4 /5 /7; only AF undefined, modelled as TEST is) or `MOV r, 0`. Controls at 0, 1, 63, 64, 65 and 10^12 in `lib/_tests/native/function_ir/function_ir_lower_tests.hthr`; mixed shift/binary DAGs end to end in `native_program.rs` (`programs_with_shifts_execute`). One immediate `SHL r, imm8` per shift waits on [[x86-undefined-flags]] (OF undefined past count 1).
