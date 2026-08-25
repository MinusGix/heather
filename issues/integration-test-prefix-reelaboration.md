---
title: Stop rebuilding the same prelude and library state in every integration test
status: open
labels: [testing,elaboration,performance,caching]
created: 2026-08-25
updated: 2026-08-25
---

Many elaborator integration tests construct `Elaborator::with_prelude()` and
then elaborate the same checked-in module closure independently for every
test function. The declaration-verdict cache removes repeated kernel gates
where explicitly wired, but it does not remove parsing, surface elaboration,
registry construction, or warm-path hashing. As the standard library grows,
that fixed prefix multiplies by test count.

`lib_algebra` made the cost visible: 35 tests each loaded seven unchanged
modules, producing a 67.30-second target. Replaying declaration verdicts for
probe tests while retaining one ungated acceptance reduced it only to
27.61 seconds warm; the remaining roughly 0.8 second per probe is still
rebuilding the elaborator/module state.

Design a reusable checked-prefix fixture for tests. Candidate shapes include
an in-process clonable/snapshot state, a test-only immutable base plus cheap
transactional overlays, or a broader serialized artifact. Preserve fresh
diagnostics/rollback state and do not let mutations or generated content ride
on a cached verdict.

## Acceptance

- Attribute prelude, parsing/elaboration, kernel gate, and cache-walk time on
  `lib_algebra` and one unrelated standard-library target.
- Reuse the prefix without sharing mutable per-test attempts, diagnostics,
  module names, generated definitions, or resolution state.
- Keep one ungated front-to-back acceptance for each shared fixture family.
- Bring the retained four-test `lib_algebra --fast` slice below five seconds
  warm and demonstrate that adding probe tests no longer scales with prefix
  size.
- State how the mechanism works across integration-test process boundaries;
  an in-process-only clone does not solve repeated binaries.

## What it assumes from elsewhere

- **[[parallel-checking-and-caching]]** owns declaration-verdict cache trust.
- **[[warm-path-rewalks-unchanged-declarations]]** owns the analogous CLI
  warm-path walk. This issue owns test fixture state, not that CLI design.

## Log

- 2026-08-25: Filed from the first target-attribution pass. The cheap verdict
  replay lever bought ~2.4x on `lib_algebra`, but its warm residual remains
  above the desired 15-second target threshold.
- 2026-08-25: The same cheap, deliberately incomplete lever was applied to
  three more library closures, always retaining the module-only test as an
  ungated backstop: `lib_std_bitvec` 41.91 → 20.07 s, `nat_order`
  27.22 → 12.36 s, and `lib_std_int` 16.56 → 7.77 s. Together with algebra
  67.30 → 27.89 s, repeated kernel verdicts accounted for about 85 seconds
  per serial suite. The residual still rebuilds surface/elaborator state and
  remains this issue's scope.
