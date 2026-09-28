---
title: Borrow constructor arguments instead of repeatedly copying their subtrees
status: closed
labels: [elaborator,performance]
created: 2026-09-28
updated: 2026-09-28
---

Constructor elaboration copies surface argument subtrees while flattening
applications (`ctor_spine`/`ctor_spine_expected`) and while partitioning
payload, plain-child, and container arguments (`build_ctor`). For an n-deep
list spine, copying each remaining tail accumulates quadratic AST-copy work.

Borrow existing expressions through constructor routing and partitioning
instead. Preserve named/curried argument order, field skeleton alignment,
and all existing checking and inference behavior. This should not require a
shared-pointer rewrite of the entire surface AST.

Acceptance: constructor routing and construction do not clone their argument
subtrees; relevant constructor, named/curried, record and container tests
pass. Verify the behavior with an appropriate first-party measurement or
structural regression, rather than relying on noisy wall-time assertions.

[[iterative-constructor-elaboration]] owns removing native constructor
recursion. [[nested-constructor-elaboration-stack-overflow]] owns the guard
retained for other expression-elaboration routes.

## Log

- 2026-09-28: Constructor application spines, record/named argument permutation, payload
  and recursive-child partitioning now carry references to existing surface
  expressions. Constructor eta-expansion borrows the supplied arguments and
  owns only its fresh synthetic variables. Indexed and forded builders and
  index inference also accept borrowed arguments, so they do not need a copying
  adapter. No AST-wide representation change was required.

  Pointer-identity regressions pin borrowing through curried inference/checking
  spines and field permutation. Existing constructor, named argument, record
  and container acceptance tests pass. This removes the repeated copying of
  every remaining tail; [[iterative-constructor-elaboration]] separately owns
  removing recursive elaborator calls for plain constructor children.
- 2026-09-28: Final verification: plain full `scripts/test` reports INCOMPLETE (3,053 passed
  before death, 0 failed). The existing read-loop mutation group is killed at
  its CPU rail; [[read-loop-process-test-cpu-rail]] owns this unchanged harness
  failure. Constructor, standard-list, indexed/fording, named/record/container,
  unit, native certificate, and documentation checks pass. Caps and skip lists
  are unchanged. The original standard-list CLI reproducer also checks with
  the release compiler.
- 2026-09-28: The joint A/B against `350894f4`, using five interleaved cold checks of a
  400-deep monomorphic constructor spine, preserved all 28 recorded kernel
  counters across both binaries and every sample. Peak process RSS is lower in
  every after sample. The report flags host load, so its seconds are not used
  as a speed claim. The structural result is pinned by the borrowing tests:
  constructor argument routing keeps the original AST addresses, eliminating
  the sum of remaining-tail subtree copies. Raw timings and the replayable
  report are retained under `target/perf-ab` (`constructor-walk-final.json`).
