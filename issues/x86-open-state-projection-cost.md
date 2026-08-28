---
title: Make open x86 state projections check without exhausting conversion resources
status: closed
labels: [x86,elaboration,kernel,performance,proofs]
created: 2026-08-26
updated: 2026-08-27
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
- 2026-08-27: The RIP residual is fixed and public as
  `execute_normal_advances_rip`. Minimization exonerated instruction matching,
  the `DecodedInstruction` record, and sibling effect fields: direct
  `MachineState` construction projected cheaply, while one transparent wrapper
  around that construction exhausted fuel even for a fixed `MovRR`. After the
  one-head delta fix, both sides correctly rendezvoused at `next_rip`, but the
  same-head retry called the type-directed normal judgment. Since `BitVec(64)`
  is a positive record type, that judgment applied Sigma eta before neutral
  comparison, projected both `next_rip` applications, and forced their `add`
  bodies. A delta-stuck defined head is already neutral regardless of its
  result type, so the retry now compares the neutral spines directly and only
  unfolds on a genuine spine mismatch. A kernel rail uses a Sigma-returning
  definition behind forty beta steps: it passes with 16 fuel now and, under a
  mutation restoring the eta-first call, fails with `OutOfFuel`. The generic
  decoded/open-state RIP theorem checks under ordinary fuel; the x86 suite and
  full kernel differential suites remain the acceptance gate. Relational
  `TEST` remains the next independent re-run before this issue can close.
- 2026-08-27: Relational `TEST r64,r64` now lands on the unchanged ordinary
  fuel rail, closing the issue. `Execute` is the authoritative semantics: it
  existentially chooses AF while fixing CF/OF to false and deriving PF/ZF/SF
  from the discarded 64-bit AND result. `execute_normal` deliberately chooses
  AF=false only as a representative for functional clients, and a public
  coherence law proves that representative is admitted by `Execute`. Public
  laws pin the complete flag record, frame GPRs and memory, advance RIP by the
  decoded length, and construct open witnesses for either AF value; the x86
  consumer test packages both witnesses in one theorem. Thus every acceptance
  customer named here now checks without a fuel or stack increase: open GPR
  read-after-write, generic whole-state RIP projection, and ordinary
  non-emptiness of both architectural TEST outcomes.
- 2026-08-28: Post-close completeness correction. The inferred-Π application
  optimization from `dd923db` caused three older generated-term oracle
  controls to be refused when the left-inferred dependent type was not a
  usable spelling for the surrounding comparison. The obvious repairs all
  regress this issue's forcing customer: restoring stored annotations makes
  the complete x86 target exceed its 300-second rail, while a fuel-rollback
  fallback aborts after 85 seconds on a 500 MiB allocation. No kernel change
  from that investigation is retained. The correctness regression and the
  requirement to preserve this issue's performance win are tracked together
  by [[generated-term-oracle-controls-not-convertible]].
