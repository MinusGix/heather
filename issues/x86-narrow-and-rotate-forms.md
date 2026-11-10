---
title: x86 model: 32-bit operand forms, rotates and BSWAP, and the lowering that uses them
status: open
labels: [x86,native,compiler,function-ir]
area: heather-in-heather
milestone: [crypto-hash]
created: 2026-11-10
updated: 2026-11-10
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
