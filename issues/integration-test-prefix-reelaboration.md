---
title: Stop rebuilding the same prelude and library state in every integration test
status: open
labels: [testing,elaboration,performance,caching]
created: 2026-08-25
updated: 2026-09-11
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
- **[[semantic-module-images]]** owns persistent semantic reconstruction
  across process boundaries. This issue owns the test-harness forcing cases
  and their rail, not the general artifact format.

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
- 2026-08-25: The in-process snapshot candidate is viable immediately:
  `Elaborator` already has a deliberately cheap, isolated `Clone`. Three
  operation/class fixture binaries now build their fixed module plus
  class/instance prefix once per libtest worker in a thread-local `OnceCell`,
  then clone it for each ungated probe. Standalone full-target measurements:
  `operators_onto_classes` 43.61 → 25.24s, `binder_symbol_notation`
  20.37 → 8.99s, and `operation_indexed_classes` 30.75 → 22.50s. Their
  headers already named four load-bearing tests; the remaining stable matrix
  cases joined the existing `slow_acceptance_` lane, making their four-test
  fast slices 3.78 / 3.76 / 4.05s respectively.

  The same snapshot shape on the issue's original `lib_algebra` customer
  moved the 35-test full target 27.89 → 22.92s and its retained four-test fast
  slice to 3.81s, meeting the under-five-second acceptance. Its empty
  whole-library test still constructs a fresh elaborator and gates the entire
  closure front-to-back; cached bases cover only the checked-in closure, and
  every probe added to a clone is ungated. This is deliberately only the
  **in-process** half. Cross-binary reuse still consists solely of kernel
  verdict replay and remains open: a serialized elaborator snapshot or
  immutable shared build artifact needs its own trust/versioning design.
- 2026-08-29: Omega is now a forcing customer inside one integration-test
  binary, not merely across binaries. `crates/elab/tests/omega.rs` contains 27
  tests and each constructs the same prelude plus eight-module arithmetic
  prefix. Under the suite's test-thread cap, the first two workers both spend
  over 60 seconds rebuilding that prefix and the process is SIGKILLed at
  roughly 151 seconds wall by the cumulative 300-second CPU rail, before
  either test reports completion. By contrast, the one-test division binaries
  finish green at roughly 221--222 seconds each. The prefix must be built once
  and cheaply cloned, or equivalently shared without crossing `Rc`-based
  elaborator state between threads; raising the CPU rail is not the fix.
- 2026-08-29: The Omega fixture now builds that prefix once in a thread-local
  `OnceCell` and gives every case an isolated `Elaborator::clone`. A mutex
  serializes the first cache fill, although the final one-test-per-binary
  layout no longer needs concurrent workers. Neither the declaration cache
  nor the snapshot alone was sufficient: all 573 declarations hitting the
  cache still left the original 27-case process above the rail (SIGKILL at
  about 304 seconds), because restoring the checked declarations and running
  the cases remain real work. The 27 cases are therefore retained as three
  named nine-case suites in separate integration-test binaries. Warm target
  times are 220.84 seconds (core), 190.98 seconds (logic), and 173.29 seconds
  (reconstruction), each with 573 cache hits. The reconstruction suite also
  passed from an empty store in 172.98 seconds while kernel-checking 570
  declarations and accepting three intra-run hits. This restores ample
  per-process rail margin without weakening the independent ungated
  `omega_div_mod` front-to-back backstop. The compromise is reporting
  granularity: libtest now counts three suites rather than 27 cases, while a
  failing case still names its helper in the panic/backtrace. Generic cheap
  cross-binary prefix restoration remains open and would remove the need for
  this pragmatic sharding. The ordinary four-way full rail subsequently
  passed all 149 binaries (2,167 tests) in 621 seconds wall time: core,
  logic, and reconstruction took 241.88, 196.85, and 183.67 seconds under
  contention, all below the 300-second per-process limit.
- 2026-09-04: Suite cost attribution from the 2026-09-02 full-run timing table (2,685 reported target-seconds over 167 targets): omega_div_mod 320 s, function_ir_x86_control_flow 319, function_ir_x86_alu 289, omega 218, ir_pass_fuel 124, function_ir_x86_source 120, omega_logic 90 -- the top seven are 55% of the suite. CORRECTION, same day: the Omega shards (omega/omega_logic/omega_reconstruction/omega_div_mod_scaling, via omega_cases/mod.rs) and every function_ir_x86 shard ALREADY use support::semantic_test_base; a first grep missed the subdirectory. Re-measured serially with warm images (dev test profile, this worktree): omega 72 s, omega_logic 25, omega_reconstruction 15, omega_div_mod 183 (its deliberate source backstop; ~60 s of that is the prefix), lib_std_bitvec 28 (with_decl_cache per test, ~1 s prefix each), ir_pass_fuel 44 (no cache; ir_v1 declarations), function_ir_x86_alu 142. So the remaining source-only prefixes are worth roughly 60-100 target-seconds in total, and the shards' cost is their own suffix work. The larger suite lever found in the same measurement is the kernel's debug-only bounds-skip re-walk (subst.rs sub_ty/sub_tm under cfg(debug_assertions)): see [[certgen-harness-cost]] log 2026-09-04.
- 2026-09-11: 2026-09-11: the five per-case with_prelude() files now go through support::semantic_test_base plus a per-worker-thread OnceCell<SemanticImage> (the omega_cases pattern): mutual_recursion, termination_measures, decreases_unfolding, omega_measure_reduction (same nine-module prefix as semantic_omega_warmup), and lib_std_bitvec (first nine of the x86 list; the ungated run("") backstop stays on the source path). function_ir_x86 got a prefix-length-keyed memo over its 17 semantic_test_base sites, lib_setoid_mergeable a per-thread memo over its 28. scripts/test's focused warmup now covers those targets. Same-instance fast lane: 1095 -> 487 target-s, tests wall 202 -> 72 s; lib_std_bitvec 98 -> 12 s, so the 'half is its own conversions' estimate was wrong — the with_decl_cache prefix was nearly all of it. ir_pass_fuel (28 s, prefix 1%) deliberately untouched. Remaining source-only prefixes: warnings.rs (26 with_prelude calls), operators (12), implicit_args (11) — all prelude-only, cheap each.
