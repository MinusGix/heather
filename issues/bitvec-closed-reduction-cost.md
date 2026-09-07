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
- 2026-08-27: The x86 relational-`TEST` probe supplied that minimized query,
  and corrected its initial attribution to state-record projection. Over open
  operands, a transparent wrapper around `bitvec::band(n, left, right)` checks
  at width 4 in about 43 ms but exhausts the ordinary 2^20 per-conversion fuel
  at width 5. A structural zero consumer checks through width 6 in about 106
  ms and exhausts fuel at width 8. Their composition checks at width 4 in
  about 25 ms and width 5 in about 154 ms, then exhausts fuel at width 6.
  Root-syntactic `band(64, a, b) = band(64, a, b)` remains about 5 ms, and a
  wrapper which accepts but ignores width-64 operands is about 1.5 ms. Thus
  neither the carrier annotation, record projection, nor the semantic linear
  work explains the cliff: delta-unfolding a wrapper exposes a separately
  built but extensionally identical structural producer/consumer expression,
  whose conversion growth is pathological at single-digit widths.

  The x86 amplification is separately useful. Whole `Flags` equality stays
  opaque and checks over direct `BitVec(64)` operands (about 0.47 s), but the
  same statement exhausts fuel when those operands arrive through
  `read_gpr(r, before)`. Fieldwise constraints also force the generic cliff.
  Permanent rails in `crates/elab/tests/lib_std_bitvec.rs` pin the cheap
  syntactic/unused controls, the last passing producer and consumer widths,
  and the first `OutOfFuel` widths. The next kernel investigation should start
  from the width-5 producer wrapper, not the whole x86 state or closed carry.
- 2026-08-27: The open producer/consumer cliff is fixed without raising the
  2^20 budget. Conversion previously delta-normalized both mismatched heads to
  completion, walking straight past a wrapper/body rendezvous. Term and type
  delta now advance one defined head at a time, advancing only the newer head
  when two differ (a body can mention only older globals), and retry structural
  comparison whenever the heads meet. That removes the single-digit cliff.
  A second cost then appeared at width 64: neutral application comparison
  recursively rechecked both stored dependent Pi annotations at every curried
  node, duplicating the same codomain tree. On conversion's required
  well-typed inputs those annotations are already forced convertible by
  typing, so the application rule now uses the Pi inferred from the recursively
  compared function for its argument and result. The permanent rail now checks
  both producer and consumer wrappers at width 64 under ordinary fuel; direct
  and unused width-64 controls remain alongside it. Kernel conversion and
  evaluator differential suites are green. This closes the open symbolic
  wrapper subproblem, but not this issue's original closed generated-carry and
  excessive-unary-arithmetic acceptance clauses.
- 2026-08-28: Completeness correction: the inferred-Π application shortcut
  above was reverted after it was bisected as the cause of three false
  `NotConvertible` oracle controls. The original annotation-directed rule is
  restored. The seven BitVec rails, including the open width-64 producers and
  consumers, still pass under ordinary fuel; the tradeoff is time rather than
  a return of the old fuel cliff. Further work should make stored annotation
  comparison/instantiation cheaper without discarding its dependent spelling.
- 2026-08-28: A generic succinct-value experiment is now owned by
  [[succinct-inductive-values]]. Saturated `u64` constructor runs and shared
  composition can represent values beyond one run without expanding their
  logical spine. This does not yet close the arithmetic acceptance here:
  experiments that produced runs automatically either regressed x86 or did
  not help the forcing customer, while `Le` consumes both logical spines and
  the machine-width `carry_add` proposition still reaches `OutOfFuel`.
- 2026-09-01: Comparison materialization supplied another small closed
  reproducer. A direct `refl` assertion for unsigned or signed 64-bit ordering
  at the `2^63` boundary exhausts ordinary kernel fuel, even as the symbolic
  theorem equating x86 `CMP` flags with `unsigned_lt_bit`/`signed_lt_bit` checks
  and staged generated comparison certificates finish in 20--28 seconds.
  Splitting the concrete conjunction into individual theorems did not help;
  the first unsigned `0 < 2^63` item alone exhausts fuel. Keep this with the
  closed producer/consumer investigation rather than raising compiler rails.
- 2026-09-07: Two data from [[bitvec-ofnat-large-literals]]. The doubling
  chain (`pow`, `twice`) that overflowed the native stack at exponent 20 is
  fixed at the representation, under [[succinct-inductive-values]]. The
  remaining resource-diagnostic clause still stands, with a sharper
  reproducer than `carry_add`: `theorem t(): nat::half(1048576) = 524288
  { refl }` through `heather check` aborts the process with a Rust stack
  overflow rather than returning `OutOfFuel`, so a merely excessive unary
  computation — course-of-values `half` is one fold step per successor —
  still takes the checker down instead of being refused.
