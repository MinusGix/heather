---
title: Decimal output and input for native programs, on add and subtract
status: open
labels: [native,stdlib]
area: heather-in-heather
milestone: [hih-tools]
created: 2026-10-26
updated: 2026-10-26
---

Round 9 of `docs/native-real-programs-plan.md` (§3.7, §6). Printing a count
needs digits, and `head -n N` needs to parse one. The ISA model has no
multiply, divide or shift, and FunctionIR's shifts are refused at lowering
([[verified-lowering-instruction-coverage]]). Neither is needed. Output
subtracts powers of ten in a bounded loop, as the burned `%*d` did
([[native-proven-formatting-api]]). Input multiplies by ten as `8x + 2x`,
by doubling with `Add`.

## Scope

- Builder library functions: format a 64-bit word as decimal into a buffer
  at an offset (POSIX `%d`, and `%*d` for `wc`'s columns), and parse a
  decimal prefix of a buffer with overflow detection.
- Each with a pure spec (`decimal_digits`), stated against the `Source` it
  lowers to, where the round can afford it.

## Done when

`wc -c` prints its count, and `head -n N` takes N from argv.

## What it assumes from elsewhere

- **[[native-source-builder]]** owns the builder.
- **[[native-source-bytes]]** owns the byte stores.
