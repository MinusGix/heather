---
title: CMP with an immediate: a comparison against a constant should not need a register
status: open
labels: [native,x86,machine-model,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-12
updated: 2026-11-15
---

A comparison against a constant puts the constant in a register first: `MOV r, imm64; XOR d, d; CMP a, r; SETcc d`. The scanner's loop tests its state against two constants on every pass (`lib/lang/lexer/lexer_span.hthr`), and each costs a register for the length of the comparison and ten bytes of immediate. An ADD's constant operand is already folded into the instruction (`AddRI8`, `AddRI32`, `File::add_known`, the planner's `Folded` place); a comparison's is not, because the machine model has no CMP with an immediate.

Found fixing [[function-ir-planner-register-pressure]], where the register was the one too many. That issue was fixed another way (a comparison may write over an operand that dies at it), so this is now about code size and one register, not a refusal.

## What it takes

- `CmpRI8` and `CmpRI32` in `lib/std/arch/x86_64/x86_64.hthr` (REX.W 83 /7 ib and 81 /7 id): bytes, length, decoding and the round trip, the flags (`sub_flags` of the register and the sign-extended immediate), `Instruction::defines`, `x86_64_kept`, `x86_64_step_forms`, the assembler's table. `AddRI8`/`AddRI32` are the template for each. This is a machine-model change, so it is Minus's to merge.
- `File::compare`: an operand in no register that `file.known` has a value for takes the immediate form when the sign extension gives the constant back (`add_immediate`'s test). `Below` and `Less` only on the right; `Same` on either side.
- The planner: `Node::register_reads` leaves out a comparison's constant operand, as it leaves out an ADD's, so `node_folds` folds the constant.

## Done when

`scan_from`'s test has no `MOV r, imm64` for `FAIL` or `DEAD`, with a control that a constant too wide for the immediate still takes a register.

## Log

- 2026-11-15: Built in PR #651: `CmpRI8`/`CmpRI32` with `CmpRight` and `File::cmp_right`, the planner leaving a folded comparison's right operand out of the reads, and `MOV r32, imm32` for constants. `scan_token`'s 64-bit immediates went from 933 to 5. A constant too wide for the immediate keeps its register: `cmp_immediate` returns `None` and `cmp_right` falls back to `find`.
