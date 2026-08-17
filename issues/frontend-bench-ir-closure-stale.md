---
title: The frontend corpus' ir_v1 import closure no longer satisfies its own imports, so --check cannot finish
status: closed
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

- 2026-08-17: FIXED (2026-08-17, managed tooling round). The two halves of the diagnosis are one bug, and point 2 has a mundane answer that is worth writing down: `enter_module` (crates/elab/src/lib.rs) inserts the module's scope into `module_scopes` at its **end**, after every written import has resolved -- so a module whose import does not resolve returns from `check_module_source` before registering anything, and the *next* module's `import` of it then fails too. One missing name (`logic`, gained by lib/std/bool.hthr) therefore reported as three broken modules. `fresh_closure_runner` reproduces the CLI's registration exactly; what it did not reproduce was the CLI's **loader**, because the closure was a hand-written list of module names in the fixture.

So the fix is not 'add logic to the list', and it is not a second walker either: crates/cli now has a `lib` target (src/lib.rs) exporting `loader`, heather-elab dev-depends on it (the same dev-dependency cycle heather-cache already uses), and `corpus.rs::closure(file)` calls `heather_cli::loader::load` against lib/ with `-L lib/std` -- the CLI's own DEFAULT_LIB. The corpus's closure is now read from the library, so it cannot drift from it again; the `:decls` case truncates the loaded root at the first `theorem` rather than a separately included copy.

Also done: the checksum assertion now prints the run's first diagnostic under the count (`Case::with_diagnosis`, filled by `fresh_closure_runner`, which records the first error of the closure -- the one that explains the cascade).

## What it assumes from elsewhere

- **[[frontend-benchmarks]]** owns the suite. Assumed here: only that
  `--check` is the gate a round is expected to run, and that the heavy cases
  are guarded by the checksum rather than by validation.

## Acceptance

`scripts/bench-frontend --check` completes on a clean tree, with the `ir_v1`
closure actually checking, and re-records the heavy numbers if the working
closure's cost differs from what is in the baseline.
- 2026-08-17: Acceptance met, closing. `scripts/bench-frontend --check` completes on a clean tree with the `ir_v1` closure actually checking (4 modules: logic, bool, nat, ir_v1) and the untruncated `ir_v1.hthr` case running for the first time since the breakage -- 3.78 s against its unchanged 150 s latency budget, so the suite's headline budget is enforced again rather than aborted past. The heavy rows were re-recorded, with the reasoning and the evidence that the drop is a real speedup on [[frontend-benchmarks]], which owns the baseline.

Three things this issue raised and each has an owner: the checksum's message is fixed here (it prints the first diagnostic under the count); the checksum's *substance* is fixed here too and better than asked -- it is now the closure's Psi-binding count rather than its error count, so a fixture doing less work fails instead of getting faster, and validating a heavy case is affordable again (~4 s, not ~90 s) so every corpus case validates at setup. Nothing is deferred from this issue's scope. Filed alongside, both found while verifying the fix and neither in this issue's scope: [[frontend-bench-baseline-host-string]] (the time half of the gate had been silently off on this machine) and [[frontend-bench-heavy-contaminates-cheap-cases]] (with it back on, the heavy cases contaminate later families by 1.3-1.5x).
