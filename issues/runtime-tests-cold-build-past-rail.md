---
title: runtime_tests' own build passes the library gate's CPU rail on a cold store
status: open
labels: [testing,performance]
area: infrastructure
created: 2026-11-08
updated: 2026-11-08
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
