---
title: A sampled skip check walks the whole skipped term: twenty times a generator module's check
status: open
labels: [performance,testing,kernel]
area: infrastructure
created: 2026-11-13
updated: 2026-11-13
---

The kernel's debug self-checks (`crates/kernel/src/checks.rs`) re-derive one claim in sixteen. For a substitution's skip the derivation is the whole walk the skip stepped over, so a check costs the size of the skipped term while the skip cost a constant. The module docs expect "a few percent"; on a module of `runtime fn` generators the sample is more than twenty times the module, and those modules were most of the library gate's cold build step under the test profile's binary.

Found while looking for the slowest part of `scripts/test --pr` (2026-11-13). [[runtime-tests-cold-build-past-rail]]'s 2026-11-13 log entries saw the same ratio from the other side: SHA-256's compression checked in under a minute with the release binary and ran fourteen minutes under the test profile's.

## Measured

Four-core cloud box, master a197caf, the test profile's `heather`, width one.

One module, a renamed copy of `lib/native/crypto/sha256_schedule.hthr` (93 lines, three `runtime fn`s) over a store that holds its closure; every declaration's verdict came from the store, so this is elaboration alone:

| binary | level | seconds |
|---|---|---|
| test profile | sampled (default) | 195 |
| test profile | off | 8.7 |
| release | (no checks compiled) | 7.7 |

Stack samples of the first row are all `shift_global` under `checks::rederive` (`Claim::Skip`), reached from `host.rs`'s `reify` → `same_ty` → `partial_ty`: the generator shifts the same large closed terms again and again, each shift a constant by its bounds, and every sixteenth walks the term.

The gate's build step (`heather check --build-jobs 4 --build-only lib`, stale images) over the sentinel's image seed of c4ae57c, 53 commits behind:

| level | modules built | wall | summed child time |
|---|---|---|---|
| sampled | 392 (the rest were built by hand first) | 835 s | 2387 s |
| off | 535 | 284 s | 1125 s |

Over the 392 modules both runs built: 2387 s against 845 s. Ten modules were 1427 s of the first run (`sha256_schedule` 201, `sha256_stream` 172, `runtime_held_tests` 168, `runtime_held_call_tests` 162, `sha256_working` 142, …); with the checks off the largest module is `native_compile_correct` at 45 s and none of those ten passes 16 s. Modules without generators moved little (`trig_law` 12 → 9).

## What landed

The policy is the harness's, as `checks.rs` says it should be:

- `heather` reads `HEATHER_KERNEL_SELF_CHECKS` (`off`, `sampled`, `full`; anything else is refused) and sets the kernel's level (`crates/cli/src/main.rs`). A release binary has no checks and ignores it.
- `scripts/test --fast` and `--pr` export `off` unless the caller set it. So the library gate, the showcase gate, `write-elf` and `compile-x86` children run without the sample in the stale-image lanes. The default (exact) lane, which the sentinel runs nightly, keeps it, and so do the test binaries' in-process kernels in every lane.

That is the two tiers of [[testing-architecture]]: the round lanes take the unverified fast path, the sentinel runs the reference.

## Left open: make a check cost what a skip saved

The sample should be bounded by work, not by count, so the default level is affordable everywhere (the sentinel's `library.rs` is over half of its suite's CPU, and the in-process elab tests still pay). Directions, all in the kernel and so for Minus:

- Spend checks from a budget fed by the nodes ordinary traversals walk: verify a sampled skip only while the nodes re-walked so far are under a fixed fraction of the nodes walked. It stays a function of the claims a run makes.
- Check a node's skip claim once per mapper and depth rather than every sixteenth time it is made: the claim is about the node, and the generator makes the same claim about the same node thousands of times.
- The comparison after the walk (`mapped == **t`) is a second traversal of the same term.

## Done when

A debug build's cold check of `sha256_schedule` at the default level is within a small factor of its check with the checks off, and `scripts/test` no longer needs to set the level.
