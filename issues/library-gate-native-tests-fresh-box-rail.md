---
title: The library gate's lib/_tests/native folder exceeds the CPU rail on a fresh box
status: closed
labels: [testing,performance,caching,images]
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

## Cause

Not the native closure's size. The seed was written at a24a2b3, before
#360 and #359 bumped the semantic image format (`HTHMOD\0\x1e`, interface
`HTHIFC\0\x1b`), and the format was in neither the module cache key nor the
build planner's probe:

- `BuildPlan` decides what is built from `ModuleImageCache::recorded_interface`,
  which reads the 136-byte header alone. The header's cache magic and key
  still matched, and under `--accept-stale-images` an image of another build
  is accepted, so every seeded image counted as built: the step built 3
  modules (64 on the layered-registry branch, whose sources differ).
- Every load decodes the section and refused it (`stored module `pair` is
  unusable (semantic image was rejected: unsupported module-image format) —
  rebuilding`). `pair` and `morphism` sit low in the std chain, so their
  rebuilt interface hashes moved the key of every module above them: plain
  misses, elaborated in the folder child itself. That is the 6244
  declarations kernel-checked and the 5 modules replayed, and
  `perform_call`'s 116 s was its elaboration, not a replay.

Any folder whose closure passes `pair` is exposed the same way, which fits
`lib/_tests/std/analysis` being killed cold on #318. #358, #359 and #366
each ran `--pr` on a box seeded before the bump. The exact lane never hit
it: there a stale image is a miss for planner and load alike.

## Fix

- `ModuleCacheKey::for_source` (and the relocation candidates'
  `SourceIdentity`) hash `heather_elab::image_format()`, both encodings'
  versions; `DOMAIN_KEY` is `/4`. A bump is now a clean miss everywhere, so
  the build step builds the closure a module per process, each under its own
  rail.
- `recorded_interface` also checks the semantic section's version, so
  "built" means what a load accepts even for an image written at its key
  with another section.
- `crates/cache/tests/module_images.rs::an_image_of_another_format_is_never_counted_as_built`;
  `docs/module-dag-design.md` §12.

## Measurements (cloud box, dev binary, one kernel worker, 300 s rail)

| store | build step | `lib/_tests/native` folder |
|---|---|---|
| empty, master | 290 built, 522 s wall | 52 s, exit 0 |
| sentinel seed, master, stale lane | 3 built, 2 s | killed at 300 CPU-s |
| sentinel seed, this change, stale lane | 290 built, 522 s wall | 52 s, exit 0 |
| this build's images, read by a build with another elaborator fingerprint (stale but decodable), no verdict store | 51 built (refusal images), 123 s | 70 CPU-s, exit 0 (540 kernel-checked, 185 vouched whole) |

So the stale-decodable case, an ordinary `--pr` after an elaborator edit
on a seeded box, stays well inside the rail; only the format mismatch broke
it.

`native_compile_correct::Target::perform_call` is a large item, but it is
elaborated in a build process of its own, not in the folder child, so it
does not need a split for this gate.

## Log

- 2026-11-02: Filed from the layered-registry round.
- 2026-11-02: Closed: the planner and the load disagreed about old-format
  images; the key and the probe now cover the format (thread "Stop native
  gate resource kills").

