---
title: Closed BitVec computation over generated values exhausts stack and memory below machine widths
status: open
labels: [stdlib,bitvectors,kernel,conversion,performance]
created: 2026-08-26
updated: 2026-08-26
---

The executable carry round exposed two different cost regimes which must not be
treated as one fuel problem.

First, deciding the arithmetic specification
`pow(2,n) <= toNat(a) + toNat(b)` at closed values asks the current unary `Nat`
representation to materialize exponentially large values. Under the ordinary
debug test rails, a forced `refl` computation over `all_ones(n) + one(n)`
measured 1 ms of final kernel-gate time at width 4, 25 ms at width 8, 318 ms at
width 12, and overflowed the test thread stack at width 13. Width 64 is not a
plausible fuel adjustment: its threshold alone has `2^64` successors.

Second, the structural `carry_add_bit` has only linear semantic work, but a
forced closed computation over the same generated values measured 4 ms at
width 8, 48 ms at width 16, 178 ms at width 24, overflowed the stack at width
32, and reached the 4 GiB process cap at width 64. A control implementing the
same carry propagation as a direct recursive Boolean loop completed all 64
steps in 56 ms of kernel-gate time. Therefore this second cliff is not inherent
in carry or recursion depth. It lies in the composition of generated
`BitVec` values (`all_ones`/`one`) with the dependent `head_bit`/`tail_bits`
consumer, or in conversion's representation of that composition.

Minimize the structural reproducer across these axes: one generated input
versus two, `repeat_bit` versus an already-constructor-headed value, head and
tail demanded together versus separately, and value-domain conversion versus
the syntax oracle. Instrument fuel spent, evaluator native-stack depth, forced
closures, and retained nodes. The kernel's fuel contract says resource-bounded
reduction returns `OutOfFuel`; a stack overflow or allocator abort before that
verdict is independently a correctness defect in the checker implementation.

Acceptance has two parts:

- closed structural carry at widths 32 and 64 computes under the ordinary
  stack and 4 GiB rails with growth consistent with the 64-step direct control;
- an intentionally excessive unary arithmetic computation terminates with a
  resource diagnostic rather than taking down the process. Improving its
  asymptotic representation is a separate representation/compiler decision,
  not acceptance for the structural fix.

## What it assumes from elsewhere

- **[[bitvec-executable-carry-correspondence]]** supplies the proof that the
  structural computation implements the arithmetic specification. This issue
  does not replace that refinement boundary.
- **[[x86-open-state-projection-cost]]** owns the wider state/projection
  reproducer. Reuse a common kernel fix if minimization shows the same cause.
- **[[whnf-sharing-term-growth]]** is the prior sharing failure and value-domain
  repair. This issue must first test whether the new shape is a missed member
  of that class rather than assume a new mechanism.

## Log

- 2026-08-26: Filed from bounded probes after the carry correspondence landed.
  Times exclude cached standard-library declarations and attribute only the
  probe declaration's final kernel gate where stated. Scratch probes were
  removed after measurement.
- 2026-08-26: Structural half diagnosed and fixed. Direct calls to both
  conversion domains reproduced the shape, so this was not value-domain
  disagreement. At width 32 the value machine completed in 8,496 fuel units
  with maximum native evaluation depth 5; leaking its returned value passed,
  while dropping that same value overflowed. The crash was recursive Rust
  destruction following unique thunk-memo/value edges after successful
  evaluation. `TmClo` now takes a unique computed-value edge into a
  per-thread iterative destruction worklist; a 100,000-node value/closure
  chain is the kernel regression.
- 2026-08-26: The separate width-64 allocation cliff was the library
  algorithm's lazy accumulator. Passing `carry_majority(...)` unevaluated to
  the recursive call retained the preceding projected operands in every
  accumulator thunk. A two-vector zip, one-vector scans, and a direct 64-step
  Boolean loop were controls; explicitly forcing each next carry made width
  64 check in about 0.54 s. `carry_bits_next` now performs that force, and
  `carry_bits_step` preserves the open arithmetic correspondence proof. The
  routine bitvector suite pins the formerly fatal closed width-64 case.
  Remaining before this issue closes: preempt an inherently excessive unary
  arithmetic computation with `OutOfFuel`/a resource diagnostic instead of
  allocator failure.
- 2026-08-26: The evaluator graph is now query-arena-backed, replacing the
  temporary thread-local destruction worklist; successful forced values live
  in bounded 16K term/type FIFO caches. Explicit `ValueMetrics` instrumentation
  measured the isolated closed width-64 structural carry under the ordinary
  rail: 841 conversion/analyzer arenas, 3,946 environment nodes, 113,890 term
  closures, 12,546 type closures, and 133,672 term-cache lookups (25,122 hits,
  108,550 inserts, 92,165 evictions; peak exactly 16,384). A controlled 32K
  capacity run left lookups and hits effectively unchanged (133,672 / 25,128)
  and reduced evictions by almost exactly the extra 16K slots. This is a
  streaming working set, not evidence that 16K narrowly misses a hot set;
  retaining twice as many values buys no sharing and is not landed. The next
  lever is allocation/force shape or a smarter admission policy, guided by a
  minimized producer/consumer query, rather than a larger FIFO.
