---
title: Instruction coverage for the verified lowering beyond add, sub and the bitwise ops
status: open
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-21
updated: 2026-11-10
---

The verified lowering ([[function-ir-verified-lowering]]) selects only
what the ISA model can state. That is Add, Sub, And, Or, Xor, MOV of
registers and immediates, CMP with SETcc, TEST, and Jcc/Jmp, with CALL,
RET and stack moves in round 3. Round 1 refuses shifts because the ISA
model has no shift instruction. Multiply, divide, sign and zero extension
at other widths, LEA, and the immediate ALU forms are absent too. Round 4
names only the immediate forms and CMP-and-Jcc as coming back.

`tr` needs none of this. The second program almost certainly needs some of
it, and every instruction added later is a new case in the lowering's
theorem, so it is better to see the whole list now than to add
instructions one blocked program at a time.

Found while mapping the native state for Minus (2026-10-21); filed at his
request.

## Scope

- A list of the FunctionIR operations the verified lowering must cover for
  the programs the roadmap names (filters, `wc`, the parser library's
  first native client, the lexer for `hih-self`). Each entry names the x86
  forms it needs.
- For each form, the ISA model's step rule (owned by
  [[x86-64-machine-model]]), then a selection rule with its case in the
  lowering's theorem.
- Order the list by first consumer, not by convenience.

## What it assumes from elsewhere

- **[[x86-64-machine-model]]** owns the ISA model's coverage and its ledger.
- **[[function-ir-x86-shift-legalization]]** owns the semantics gap
  between FunctionIR's shifts and x86's masked counts. Assumed here: only
  that a shift selection rule waits on it.
- **[[function-ir-verified-lowering]]** owns the lowering's rounds.

## Log

- 2026-11-08: i64 round 3: shifts are selected now (chains of `SHL/SHR/SAR r64, 1` after `ShiftOp::legalize`); multiply and divide wait on [[x86-undefined-flags]].
- 2026-11-08: 2026-11-08 round 4: shifts by a constant are one `SHL/SHR/SAR r64, imm8` (`ShiftImm`); IDIV is [[x86-idiv-signed-division]].
- 2026-11-10: `docs/native-lexer-crypto-roadmap.md` §2 piece 6 orders the forms by
  customer. First group, for SHA-2 and the byte scanner: 32-bit operand forms
  (with their zeroing of the upper half), rotates and `BSWAP`, byte compares
  ([[x86-narrow-and-rotate-forms]]). Second group, for Poly1305 and field
  arithmetic: `MUL`/`MULX`, `ADC`/`SBB`, `ADCX`/`ADOX`
  ([[x86-wide-multiply-and-carry]]). `CMOV` belongs with constant time
  ([[native-constant-time]]). SIMD and SHA-NI are explicitly not scheduled.
