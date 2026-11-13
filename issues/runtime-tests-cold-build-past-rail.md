---
title: runtime_tests' own build passes the library gate's CPU rail on a cold store
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-11-08
updated: 2026-11-13
---

`lib/_tests/native/runtime/runtime_tests.hthr` costs about 370 CPU-s of its
own items at width one (`HEATHER_KERNEL_WORKERS=1`, fresh store, release
binary, cloud box), the rest of the 530 CPU-s run being its closure. The
library gate (`crates/cli/tests/library.rs`) builds each module in a
`heather check` of its own under the suite's per-process CPU rail, so on a
store with no image of it the build step is killed (`build: runtime_tests
(signal: 9 (SIGKILL))`) and the `lib/_tests/native` folder fails, though the
module checks (`--expectations`, 4 refusals matched) when run uncapped.

Seen on the class-carrier-arithmetic-surface round's `scripts/test --pr`
(twice, the second time with every other module built ahead). Master costs
the same: `scripts/timings --diff` of a width-one check of the module on
master 83c825d and on the branch has identical count columns and the same
seconds, so the diff does not reach it; a fresh container's store simply had
no image for it.

The heaviest items are `byte_class` (≈61 s), `top`, `spread`, `scaller`,
`byte_class_pair` and `choose` (30–45 s each), the runtime-fn generator's
agreement proofs (see [[runtime-fn-caller-agreement-fuel]]).

## Direction

- Split the module so no one file's build carries this much, or move the
  heaviest probes beside the natives they exercise; or
- have scripts/test warm it before the gate the way `native_closure_warmup`
  warms the natives' closures (PR #435).

## Acceptance

- A `scripts/test --pr` on a fresh container passes the library gate's
  `lib/_tests/native` folder.

## Log

- 2026-11-09: Seen again on the frame-and-locale-foundations round's `scripts/test --pr` (fresh container, gate killed at the rail); the module checks uncapped on the branch (4 refusals matched).

## Log

- 2026-11-13: PR #551 met this with a new library module: SHA-256's compression as methods of `Sha256` checked in under a minute with the release binary and ran some fourteen minutes of CPU under the test profile's, nearly all of it the `runtime` generator's elaboration of callers ([[runtime-record-function-limits]]). It is three modules now (`sha256_schedule`, `sha256_working`, `sha256_compression`), each inside the rail, and the round was flattened to cut the heaviest function. The ratio between the two binaries on a generator's run is what to look at: the kernel's share was under a second per function in both.
- 2026-11-13: PR #551: the linked-assembly gate met the same cost. With `sha256_stream` over the context's functions, an export's closure is four generator-heavy modules (`sha256_schedule`, `sha256_working`, `sha256_compression`, `sha256_stream`), and `native_linked.rs`'s first `compile-x86` children built them all cold under one rail each: three were killed at it. `scripts/test`'s `native_closure_warmup` now also builds the modules `EXPORTS.tsv` names, a module per process. Over an empty store under the test profile's binary each is inside the rail; the heaviest is `sha256_schedule`, at about five sixths of it, which is the margin to watch (a caller's generation carries its callee's program, issues/runtime-record-function-limits.md).
- 2026-11-13: PR #551: the stream's methods of `Sha256` as one module (`put`, `push`, `zero`, `pad`, `close`) ran at the library gate's rail under the test profile's binary (the lane passed with the process at the rail's last second), so the padding is `sha256_padding.hthr` beside `sha256_filling.hthr`. A caller of `Sha256::run` carries the compression's whole program in its generation, and three do (`push`, `pad`, `close`): that is what a module of them costs. After the split the heaviest of the SHA-256 modules is still `sha256_schedule`, at about five sixths of the rail.
- 2026-11-13: The ratio between the two binaries on a generator's run is the kernel's sampled self-check, not optimisation: `sha256_schedule` elaborates in 195 s with the sample and 8.7 s without it under the same test-profile binary ([[kernel-self-check-cost-on-skipped-terms]]). The stale-image lanes now run the binary with the checks off, and no module of the gate's cold build step passes a sixth of the rail there.
