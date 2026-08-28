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
- 2026-08-27: Re-tested after the arena-backed evaluator and bounded conversion
  caches landed. The generic open `read_gpr(r, write_gpr(r, value, before)) =
  value` law now kernel-checks under the ordinary rail after finite elimination
  of `r`, and is public as `read_gpr_after_write`. The stronger open
  `execute_normal(decoded, before).rip = next_rip(before.rip, decoded.length)`
  law still fails: leaving the instruction neutral produces an unsolved
  conversion goal; splitting both instruction forms reaches kernel
  `OutOfFuel`. Factoring state construction through a generic commit function
  checks the commit projection itself, but transporting it through the open
  `execute_normal` application still reaches `OutOfFuel`. This isolates the
  remaining acceptance gap to conversion of the open whole-state projection,
  rather than GPR function update, arithmetic, or instruction branching.
- 2026-08-27: A follow-on `TEST r64,r64` spike reproduced the same boundary
  below whole-machine state. The intended relation fixed registers and five
  defined flags while permitting either AF value. Open witnesses for both AF
  choices reached kernel `OutOfFuel` whether the flag constraint was one
  record equality or separate field equalities. An indexed proof constructor
  would avoid converting those equalities, but indexed families currently
  permit only `Nat` or inductive indices; `Flags` and `BitVec` are records, so
  the language correctly refused that encoding. The uncheckable spike was
  removed. Keep relational `TEST` as the next architecture forcing customer
  after this conversion boundary is repaired; do not weaken its semantics or
  retain a relation whose ordinary non-emptiness witness cannot kernel-check.
- 2026-08-27: Minimization moved the primary owner to
  [[bitvec-closed-reduction-cost]]'s explicitly requested producer/consumer
  query. A direct whole-`Flags` constraint over open `BitVec(64)` operands
  checks while keeping the computation opaque; substituting the same operands
  as `read_gpr(r, before)` exhausts fuel, and exposing any computed flag hits
  the generic symbolic BitVec cliff first. The smallest reproducer no longer
  mentions x86: a wrapper around open `band` passes at width 4 and exhausts
  2^20 fuel at width 5. Keep this issue for the additional whole-state/RIP and
  function-backed-GPR amplification, but fix and re-run the generic width-5
  rail before changing `MachineState`, `Flags`, or the architectural relation.
- 2026-08-27: The generic symbolic BitVec owner above is repaired: its former
  width-5/8 rails now pass at width 64 under default fuel. Re-running the x86
  customers narrows, rather than closes, this issue. The open
  `execute_normal(decoded, before).rip` theorem still reaches `OutOfFuel` after
  splitting `MovRR`/`AddRR`, and a restored relational `TEST r64,r64`
  non-emptiness witness still does likewise even when the existential AF
  witness is the same open variable on both equality endpoints. Inferred-Sigma
  projection comparison and raw-term syntactic reflexivity were tested as
  follow-on levers and did not move that result, so neither was retained.
  The unusable TEST spike was again removed per this issue's acceptance rule.
  The residual is now demonstrably outside the transparent open-BitVec
  producer/consumer defect and remains owned here.
