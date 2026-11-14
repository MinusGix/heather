---
title: x86 model: 32-bit operand forms, rotates and BSWAP, and the lowering that uses them
status: open
labels: [x86,native,compiler,function-ir]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-14
---

The machine model's instructions are 64-bit two-register forms, immediates
for `ADD`, and shifts (`lib/std/arch/x86_64/x86_64.hthr`, `Instruction`).
`docs/native-lexer-crypto-roadmap.md` §2 piece 6 orders what the two
targets need next; this issue owns the first group. It is the "order the
list by first consumer" that [[verified-lowering-instruction-coverage]]
asked for, now that the consumers are known.

## Scope

In consumer order, each with its step rule, encoding round trip and flags
(through the undefined-flags mask):

1. 32-bit operand-size forms of `MOV ADD SUB AND OR XOR CMP TEST` and the
   shifts, with the rule that a 32-bit write zeroes the upper half. They
   make a narrow operation one instruction where the masked route is three.
2. `ROL`/`ROR` by an immediate at 32 and 64 bits (`RORX` if BMI2 is taken
   as a target fact).
3. `BSWAP` (or `MOVBE`), for big-endian block loads.
4. `MOVZX` register forms and 16/32-bit loads and stores.
5. `LEA`, for a table index and for position-independent addresses.

The selection rules and their cases in the lowering's theorem are
[[function-ir-narrow-arithmetic]]'s and
[[verified-lowering-instruction-coverage]]'s.

## Done when

Each form decodes, steps and round-trips in the model, with a negative
control per group (a 32-bit `ADD` that leaves the upper half is refused),
and SHA-256's Σ1 from [[sha2-compress-native]]'s probe certifies.

## What it assumes from elsewhere

- **[[x86-64-machine-model]]** owns the model's scope and its coverage
  ledger.
- **[[x86-wide-multiply-and-carry]]** owns the next group.
- **[[rotate-idiom-pass]]** owns recognising a rotate written as two
  shifts; here the rotate is emitted only where the source spells one.

## Log

- 2026-11-10: The probe named under "Done when" certifies without this issue: SHA-256's Σ1, and then its whole `T1`, `T2` and schedule word, compile through the narrow lowering of [[function-ir-narrow-arithmetic]], which settles with two 64-bit shifts and adds nothing to the machine model. So group 1 here (32-bit operand forms) is no longer on the route to a working SHA-256; it is an optimization of it, removing the settle at width 32 ([[function-ir-narrow-settle-lazily]] removes most of the others at every width). `ROR`/`ROL` likewise: each rotation is five instructions as a shift pair and would be two. `BSWAP`, the 16/32-bit loads and `LEA` are still on the route, for block loads and the constant table.
- 2026-11-14: Two forms added, each checked against the SDM, `as` and the processor (`lib/_tests/std/arch/x86_64/x86_64_narrow_forms_tests.hthr`, rows in `docs/optimizer-design.md` §10): `MovSelf32` (`MOV r32, r32` with one register in both fields, the 32-bit settle) and `RorRI32` (`ROR r/m32, imm8`: the count masked to five bits, the upper half cleared at every count, CF the result's bit 31 and OF undefined at a nonzero count, the other flags kept). The lowering uses the first for every settle at width 32 and the second for the new `RotateRight(32, …)` node at counts below 32. Still open here: the 32-bit ALU forms (`ADD r32` would drop the settle after a sum altogether), `ROL` and the 64-bit rotate, `MOVZX`, `LEA`.
