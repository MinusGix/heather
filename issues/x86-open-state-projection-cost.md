---
title: Make open x86 state projections check without exhausting conversion resources
status: open
labels: [x86,elaboration,kernel,performance,proofs]
created: 2026-08-26
updated: 2026-08-26
---

The first register-only x86 module checks, including generic `MOV` memory/flag
frame theorems. A more general theorem saying every current instruction sets
`rip` to `next_rip` exhausted default kernel conversion fuel even after the
uniform RIP/memory commit was factored outside instruction-specific effects.
A closed read-after-register-write probe likewise exhausted fuel, and forcing a
closed whole `ADD` effect overflowed the test thread stack or reached the 4 GiB
process cap.

This resembles the existing large-record/projection annotation cost family,
but the new customer is valuable enough to retain as its own reproducible
boundary. Minimize it before choosing a fix: determine whether the cost comes
from `MachineState`/`RegisterEffect` record projection annotations, the
function-backed `Gprs`, eager conversion of sibling flag fields, or their
combination. Acceptance is an open fallthrough theorem and a register
read-after-write law under the ordinary fuel and 4 GiB/stack rails. Do not raise
fuel or stack as the fix.

## What it assumes from elsewhere

- **[[unnameable-annotation-occurrences]]** owns the general core-sharing and
  projection-annotation investigation. Assumed here only: reuse a general fix
  if this reproducer is another instance of that mechanism.
- **[[x86-64-machine-model]]** owns the state and instruction semantics. This
  issue owns proof/elaboration cost, not their architectural meaning.

## Log

- 2026-08-26: Filed from the first executable `MOV`/`ADD` vertical slice. The
  definitions and narrower frame theorems kernel-check; only projections that
  force the wider open/closed state are withheld.
- 2026-08-26: The carry follow-up split one part of the closed `ADD` failure
  into [[bitvec-closed-reduction-cost]]. A direct 64-step Boolean loop checks,
  while `carry_add_bit` over generated closed `BitVec` operands overflows below
  width 64. Keep this issue focused on the remaining state/record projection
  axes after that generic reproducer is minimized.
