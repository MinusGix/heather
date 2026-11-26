---
title: Decode P3109 codes by shifts, not unary division
status: closed
labels: [mathematics,floating-point,evaluation]
area: mathematics
milestone: [math-float]
created: 2026-11-26
updated: 2026-11-26
---

`Format::code_mag`/`code_bexp` (`lib/std/num/float/p3109_codes.hthr`) decode a
code by `Nat::div` and `Nat::mod`, and `Nat::div` counts its quotient out one
unit at a time (`lib/std/num/nat.hthr`, `divmod_step`). The 8-bit value-table
probes had to be split into 16-code stage theorems (8 for Binary8p3ue), and
`Rat::floor_nat` ran out of fuel at Binary8p3se's top until it moved to
`ldiv` (docs/library/float-p3109-design.md §6, §7).

`half` is always `2^frac`, so the quotient is `n.shr(frac)` and the remainder
`n - (n.shr(frac)).shl(frac)` (or a mask). Restate the two through shifts,
keep `code_parts` as the bridge (the proofs use only `div_mul_add_mod`,
`mod_lt` and `div_mod_unique`, which become lemmas about the shift), and
check whether one 256-code table then fits the budget, and a 16-bit format's
table at all.

## What it assumes from elsewhere

- **[[nat-wide-evaluation]]** owns evaluating `Nat::pow`/`ldiv` at large sizes.
  Assumed here: nothing; this removes a division rather than speeding one up.

## Log

- 2026-11-26: LANDED: code_q/code_r by Nat::shr with the code_qr bridge; a probe showed Nat::div(65000, 32) out of fuel where shr and ldiv finish at once. Tables are 256-code stages now and cover Binary10p5se and Binary12p7se as well (21 formats).
