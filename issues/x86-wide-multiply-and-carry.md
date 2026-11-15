---
title: x86 model: widening multiply and carry chains (MUL, MULX, ADC, SBB, ADCX/ADOX)
status: open
labels: [x86,native,compiler,cryptography]
area: heather-in-heather
milestone: [hih-crypto]
created: 2026-11-10
updated: 2026-11-10
---

The second instruction group of `docs/native/native-lexer-crypto-roadmap.md` §2
piece 6, needed from stage C4 (Poly1305, then field arithmetic for
X25519): the machine model has no multiply and no carry chain.

## Scope

- `MUL` and `IMUL` (64 × 64 to 128 in RDX:RAX; the two- and three-operand
  `IMUL`), `ADC` and `SBB`, `CMOVcc`, and the remaining `SETcc` conditions.
  `MULX`, `ADCX` and `ADOX` if BMI2/ADX are taken as target facts.
- FunctionIR nodes for the widening multiply and add-with-carry, valued by
  [[bitvec-rotates-and-wide-ops]]'s `mul_wide` and `adc`.
- The leakage contract's line for each ([[native-constant-time]]): `MUL`
  and `CMOV` are on Intel's data-operand-independent list, and the model
  should say which list it assumes.

## Done when

A 2 × 2 limb multiply with carries certifies and agrees with its Heather
function at `Nat`, through `mul_wide` and `adc`'s `toNat` readings.

## What it assumes from elsewhere

- **[[x86-narrow-and-rotate-forms]]** comes first.
- **[[x86-idiv-signed-division]]** owns division, which neither roadmap
  target needs.
- **[[field-arithmetic-language]]** is the customer: its compile strategy
  emits these instructions and nothing else in `rt` needs them yet.
