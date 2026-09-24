---
title: A Rust edit's loop is build-bound: 61-77 s of build before 33 s of fast-lane tests
status: closed
labels: [testing,performance,build]
created: 2026-09-24
updated: 2026-09-24
---

After [[suite-tests-reelaborate-library-modules]] and [[fast-lane-heaviest-declarations]]
cut the fast lane's test phase to ~33 s, the edit → green loop after a Rust
edit is dominated by **building** the tests, not running them. This issue owns
the measurement and the ranking of levers; each lever is its own issue.

## Measurement (2026-09-24, 16-core desktop, warm target dir)

A one-line behaviour-neutral body edit (`std::hint::black_box(())`), then the
build with `cargo test --workspace --no-run --timings`, then `scripts/test --fast`
(all three runs green, 2765 passed):

| edit | build | fast-lane tests | loop |
|---|---|---|---|
| none | 0 s | 32 s | 33 s |
| elab body (`kernel_workers_from_env`, lib.rs) | 77 s | 35 s | ~112 s |
| kernel body (`nat_residual`, eval.rs) | 61 s | 36 s | ~97 s |

The build's wall, from cargo's unit timeline:

- `heather-elab` lib: 22–24 s (codegen 18–22 s at `opt-level = 3`), even for
  a one-line edit; a kernel body edit re-codegens it just the same.
- elab's in-crate unit tests (`heather_elab "lib" (test)`, a second full O3
  compile of the crate under `cfg(test)`): ~40 s, and it is the **last unit
  to finish** in both runs. It cannot start before the elab → cli chain is
  built, because `heather-elab` dev-depends on `heather-cli` (elab edit: it
  started at 37.7 s and ran its last 27 s alone).
- ~200 integration-test binaries: 300–320 CPU-s summed, but spread over ~25 s
  of wall on 16 cores — CPU and disk (`target/debug/deps` holds 14.7 GB of
  executables, ~40 MB each), not the critical path.

## Levers, in order

1. [[elab-unit-tests-wait-on-cli-dev-dependency]] — start elab's unit-test
   compile at t≈0; expected build ~45–50 s.
2. [[elab-integration-test-binaries-merge]] — ~180 links → ~15; CPU and disk.
3. [[elab-rebuild-floor]] — the ~40 s unit-test compile and the ~22 s elab
   lib rebuild that remain after 1.

The test phase's CPU (native certificate size) comes after these.

## Log

- 2026-09-24: Lever 1 landed ([[elab-unit-tests-wait-on-cli-dev-dependency]]): build after an elab body edit 77 → 53 s, kernel body edit 61 → 49 s. Lever 2's design: docs/elab-test-families-design.md.
- 2026-09-24: Lever 2 landed ([[elab-integration-test-binaries-merge]]): 178 elab test binaries → 13 families + 3 standalone. Same box, same edits: elab body edit 37.5 → 29.1 s wall (263 → 92 unit-s), kernel body edit 28.8 → 9.2 s (356 → 68 unit-s); full suite 2922 passed, tests 64 s warm. Next: [[elab-rebuild-floor]], re-measured first.
- 2026-09-24: Correction: every kernel-edit build figure in this issue and its lever issues (61, 49, 26.8 s; the families round's 28.8 → 9.2 s may share the flaw) also rebuilt elab, because the measuring script reverted the elab probe edit just before the kernel one. A kernel body edit alone is ~7 s ([[elab-rebuild-floor]], 2026-09-24). The elab-edit figures stand.
- 2026-09-24: All three levers resolved (two landed, [[elab-rebuild-floor]] closed with no open lever). Next: the test phase.
