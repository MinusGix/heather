---
title: Projecting deep into a nested conjunction costs quadratically in depth
status: closed
labels: [elaboration,performance,proofs]
created: 2026-09-25
updated: 2026-09-28
---

Reading hypothesis `k` out of a right-nested conjunction as
`facts.right.right…right.left` costs about quadratically in `k`. Each
projection re-infers the type of the whole conjunction below it. In
`lib/decimal_line.hthr` (2026-09-25), `line_word_value` pulled 24 facts out of
the conjunctions its `*_arith` lemmas returned and took **28 s**. The same
facts, returned as a record with named fields (`GroupFacts`) and read by field,
brought the item down to well under a second, together with naming the states
(`line_state_*`). `elf64_read_print`'s `ReadPrintFormat` and `PrintFormatted`
are records for the same reason.

Records are the better library style anyway, since a named field documents
itself. But a conjunction is what `⟨…⟩` builds and what `omega`-style tactics
return, and a person should not meet a quadratic when reading one.

## Questions

- Is the cost in elaboration (`.right` inferring `And(A, B)` by whnf of the
  receiver's type at each level) or in the gate? Attribute one item with
  `--timings` at growing `k`.
- If elaboration: can the receiver's type be carried rather than re-inferred
  per projection? The same question is open for records at
  [[per-instantiation-projection-boundaries]].
- Is it the same mechanism as [[proof-let-substitution-cost]]? `facts` there
  was a `let` bound to a lemma call, so each projection may also have copied
  the call.

## Acceptance

- A family: a `k`-fold conjunction projected to its last component, at
  growing `k`. The cost is recorded and made linear, or its shape is
  explained.

## Log

- 2026-09-25: [[proof-let-substitution-cost]] diagnosed its mechanism (2026-09-25): the kernel's typing has no memo keyed on node identity, so a shared `let` value is re-checked on every path to it. That is plausibly the half of this cost that comes from re-inferring the receiver `facts`; the per-level `And` type computation is separate. A typing memo on node identity would fix both. Untested here.
- 2026-09-28: Reproduced, attributed and fixed the kernel's projection-prefix
  replay. The original elaboration hypothesis is inaccurate on this tree:
  `resolve_dot` recursively infers each source receiver once and passes its
  type to `project_field`. The kernel's `fst@` / `snd@` inference also walks
  the receiver once, but each value-domain view evaluates its entire deferred
  `Sel` prefix again. A chain therefore pays the sum of prefix lengths even
  when its head is a bare parameter. It needs no shared-let typing memo to
  remove that work.

  `Tc::projection_at_spine` now infers the non-projection head once and views
  all contiguous projection receivers in one short-lived arena. Every link
  still checks for a Sigma and carries the appropriate universe level and
  dependent first-component argument. Only levels and an arena-free final
  selection description return; the eager oracle and quotation translator
  retain the per-node rules. Each view gets its own fuel grant. Selection
  arguments at the ambient depth reuse its identity environment, permitting
  the arena's existing memo to share evaluations of receiver prefixes.

  Also stopped constructing a parallel emitted copy of every remaining tail
  in the elaborator's checked-projection fallback: those projections carry
  no annotations. Only the selected field's type is spelled. Component
  projections inside quotations retain their annotation preparation.

  The durable generator `probes/conjunction_projection_chain.py` emits
  `And<A, ... A>` families, projecting the last component from a bare binder
  and from an opaque identity-theorem result bound by `let`. Three interleaved
  cold `scripts/perf ab` pairs against `62b89102`, width one, reproduce these
  exact evaluator counts in every sample:

  | Depth | Bare before → after | Alias before → after |
  |---|---:|---:|
  | 4 | 81 → 36 | 192 → 48 |
  | 8 | 417 → 84 | 672 → 96 |
  | 16 | 1,953 → 180 | 2,496 → 192 |
  | 32 | 8,481 → 372 | 9,600 → 384 |
  | 64 | 35,361 → 756 | 37,632 → 768 |

  The post-fix evaluator shapes are `12k - 12` and `12k`. Selection
  evaluations are linear too; at depth 64 the bare count is 17,397 → 376.
  Whole-family steps (including prelude, logic and identity) are
  99,257 → 5,177; rescoping nodes are 509,092 → 341,914. The box was loaded,
  so no wall-time claim follows. Replayable local report:
  `target/perf-ab/conjunction-projection-chain.json` (not committed).

  End-to-end source elaboration remains superlinear: it still substitutes
  through and respells the remaining type per field. That distinct residue
  is owned by [[conjunction-projection-type-preparation-cost]]. The issue's
  acceptance allows an attributed shape; the kernel chain is made linear
  and the remaining source-type work is explained and assigned.

  Regression coverage: `annotation_cost` bounds evaluator growth at depths
  8/16/32 for both head shapes; checks open types, dependent evidence fields,
  literal and neutral computation, and wrong-value/wrong-field-type refusals.
  `typing_differential` adds dependent chains through depth 32 and invalid
  projections beyond the last Sigma at both computing layers. All five
  annotation-cost tests and all ten differential tests pass.

  Final plain full `scripts/test`: **3,060 passed, 0 failed, 5 ignored**,
  including the read-loop/read-print mutation controls and native certificate
  gates. The final focused annotation-cost rerun also covers the theorem-alias
  growth bound. `git diff --check` and `scripts/issue check` pass (one unrelated
  pre-existing tracker warning).

  The full `scripts/bench --check` rerun flags only the known stale lower
  slope bound for `wf/check-tree` (also recorded by [[wf-ih-rebuilt-per-node]]).
  Focused checks on committed `62b89102` and the changed tree both reproduce
  that flag; no benchmark baseline or band was changed. The first benchmark
  run overlapped compilation and the full suite and reported noisy timing
  flags that disappeared on the full rerun.
