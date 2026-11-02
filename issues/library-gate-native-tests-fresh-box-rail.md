---
title: The library gate's lib/_tests/native folder exceeds the CPU rail on a fresh box
status: open
labels: [testing,performance,caching]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

Keep the library gate's `lib/_tests/native` folder check inside the 300 s CPU rail on a fresh cloud box.

## Problem

On a fresh container seeded from the master sentinel (`scripts/sentinel seed`), the first `scripts/test --pr` failed `crates/cli/tests/library.rs::every_library_module_checks` with `== lib/_tests/native (signal: 9 (SIGKILL))`: the folder's child ran 300 s and met the rail. The build step had reported `64 modules built ahead, 0 failed`, so this is not [[library-gate-module-cold-rail]]'s mechanism (a module killed in the build step).

Seen in the layered-registry round (2026-11-02, branch `claude/project-thread-m8siut`), and reproduced on master 36dccd2 alone: from two fresh copies of the seeded stores, `heather check --cache --cache-dir D --expectations --accept-stale-images lib/_tests/native` (dev binary, one kernel worker, after `--build-only lib/_tests/native`, which built 3 modules) took 497 CPU-s on master and 486 on the branch, with identical `--timings` counts. The run row: about 509 s total, 134 s in the kernel gate; 6244 declarations kernel-checked against 6648 accepted from cache, 5 modules replayed. The heaviest item was `native_compile_correct::Target::perform_call` at about 116 s (23 s gate, 7.1M steps).

So the seed covers the module images but the folder still does most of its closure's declaration work in one process, and the native closure has grown past the rail since [[library-gate-native-cold-rail]] closed (heap arena, procedures).

## What would help

- Find why 6244 declarations are checked in the folder child when every module had an image (the verdict store is not seeded by design, `scripts/test`'s seed comment), and whether the build step should have left them vouched.
- `native_compile_correct::Target::perform_call` alone is over a third of the rail; a `*_close`-style split as in [[library-gate-module-cold-rail]] would shrink it.
