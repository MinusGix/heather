---
title: The frontend corpus' ir_v1 import closure no longer satisfies its own imports, so --check cannot finish
status: open
labels: [frontend,tooling]
created: 2026-08-17
updated: 2026-08-17
---

## Log

- 2026-08-17: FOUND at HEAD d180c1a while verifying the diagnostics-pair round (2026-08-17), and PRE-EXISTING -- reproduced identically in a git worktree at HEAD with no changes, so it is not that round's doing.

`scripts/bench-frontend --check` (and any run that includes the heavy cases) aborts in the harness's checksum assertion:

    fixture `ir_v1.hthr:decls` returned 3, expected 0 -- the fixture is broken,
    not slow (a checksum mismatch means the work changed)

The three errors are one per module of the closure, and they are all the same error:

    module bool: unknown module `logic`: it is not in this run's import closure
    module nat:  unknown module `bool`:  it is not in this run's import closure
    module ir_v1: unknown module `nat`:  it is not in this run's import closure

So this is not a library breakage: `heather check lib/ir_v1.hthr`, `lib/std/nat.hthr` and the truncated declarations-only prefix all check clean through the CLI. It is the fixture's closure (`ir_v1_closure` in crates/elab/benches/frontend/fixtures/corpus.rs -- `bool`, `nat`, `ir_v1`) having drifted from the module loader in two independent ways:

1. `lib/std/bool.hthr` now imports `logic`, which the closure does not list.
2. Listing is not enough anyway: `nat` cannot see `bool` even though `bool` was
   `check_module_source`d into the same elaborator immediately before it, so a
   checked module is evidently not thereby *in the closure* for the next one.
   Whatever registration the CLI's loader does, `fresh_closure_runner` does not.

Point 2 is the interesting half, and it is why the fix is not "add `logic` to the list": the fixture is timing an elaborator that fails all three modules, which means the heavy corpus numbers it reported were never measuring the closure it claims to measure. The `ir_v1.hthr` case (untruncated, budget 150 s) never runs at all, because the panic on the `:decls` case aborts the worker first -- so the suite's headline latency budget is currently unenforced.

Also worth fixing while there: the heavy cases are deliberately not validated (validating means checking the file, ~90 s), and the checksum is the only guard. That is a reasonable trade, but the checksum failure surfaces as a panic with a count and no message, which cost a detour to diagnose. Printing the first error alongside the count would have made this a one-line finding.

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the suite. Assumed here: only that
  `--check` is the gate a round is expected to run, and that the heavy cases
  are guarded by the checksum rather than by validation.

## Acceptance

`scripts/bench-frontend --check` completes on a clean tree, with the `ir_v1`
closure actually checking, and re-records the heavy numbers if the working
closure's cost differs from what is in the baseline.
