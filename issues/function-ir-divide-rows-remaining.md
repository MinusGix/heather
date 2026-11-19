---
title: Divide rows: 65-bit reciprocals, powers of two, a divisor that is a word
status: open
labels: [native,x86,runtime-fn]
area: heather-in-heather
created: 2026-11-19
updated: 2026-11-19
---

The operation rows (docs/native/dogfooding-plan.md §5.3a,
`lib/native/function_ir/function_ir_operation_x86.hthr`) offer `x / d` and
`x % d` only for a constant `d` whose odd part has a reciprocal that fits a
word (`reciprocal_fits`): 10, 100, 1000 and every divisor whose odd part
has a 64-bit multiplier. Refused today, each with a reason the lowering
names:

- **An odd part that needs a 65th bit** (7, 25, 125, about a fifth of the
  divisors below 2000): the standard fix-up `t = mulhi(x, m'); q = (((x - t)
  >> 1) + t) >> (s - 1)` with `m' = m - 2^64`. Its theorem is
  `Nat::div_by_reciprocal` read at `m = 2^64 + m'` plus the fix-up's
  arithmetic.
- **A power of two** (`o = 1`, so the multiplier is `2^64`): `x >> z`, and
  `x & (2^z - 1)` for the remainder. Either a row here or a rule of the
  optimizer that rewrites the node to the shift before lowering.
- **A divisor that is a word**: `DIV`, which faults on zero; its row waits
  on the model's blocks taking a guarded faulting instruction
  ([[x86-idiv-signed-division]]).

The rows fix registers (RAX and RDX for a divide, RCX for a shift by a
word) and the lowering forgets whatever they held. The planner keeps a
fresh value out of every register some row of the function writes
(`Operation::writes_fixed`, `StructuredRegion::rows_write`,
`Node::choose_clear_of`) while another is free; it is per function, not
per live range, so under pressure a value can still land in one and the
compile is refused, never wrong.

## Done when

`x / 7`, `x % 16` and `x / y` certify through `compile-x86`, and the
`runtime_ports` ledger's divide rows run.
