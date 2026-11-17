---
title: Let the native tests replay the library gate's images instead of elaborating the library again
status: closed
labels: [testing, performance, images]
area: infrastructure
created: 2026-11-17
updated: 2026-11-17
---

On a fresh cloud container (4 cores) `HEATHER_PR_AFFECTED=all
HEATHER_PR_NATIVE=all scripts/test --pr` spent 1286 s of a 3061 s run in
warm-ups before the parallel runner started (seeded from images a
211-module respelling had made stale). Over an empty store, timed line by
line:

| warm-up | wall |
|---|---|
| `semantic_x86_warmup` | 49 s |
| `semantic_omega_warmup` | 1 s |
| parser warm-up, four stages | 20 s |
| `native::tests::the_bundled_library_checks` | 194 s |
| `native_closure_warmup` (a module per process, then the examples three at a time) | 748 s |

The native chain was one process at a time while three cores idled, and it
elaborated modules the library gate elaborates again beside it: the native
tests' store (`target/native-test-images`) and the gate's
(`target/cli-check-images`) held images of the same files under different
keys. In a warm gate store, 73 of the 78 modules of the native closure
(`warm-native --unbuilt` over the examples and the linked exports) had no
image.

## Cause

`compile-x86` checked its bundled proof library
(`crates/cli/src/native/support.rs`) under paths `<name>.hthr`, so under
`LintProfile::Default`, and without the common prelude, which the
`// lib-closure:` lists leave out. The loader gives every module outside the
prelude's closure an implicit `import common;` and a file under `lib/std`
the stdlib profile; both are in a module's image key, and the world under a
module (its interface hashes) differs with the implicit import, so every
module above the bundled library had another key too.

## Change

- `scripts/lib-closures`: a marker word `as-loaded` lists the closure as the
  loader loads it, the common prelude included, each entry
  `("name", "lib/…/name.hthr", include_str!(…))`;
  `crates/cli/tests/lib_closures.rs` checks it the same way.
- `crates/cli/src/native.rs`: the bundled modules are checked at their repo
  paths under the profile their path gives (`bundled_modules`,
  `bundled_profile`). `compile-x86` and `warm-native` take
  `--accept-stale-images`, as `check` and `write-elf` do.
- `native_test_images()` is the gate's store; the tests call `compile-x86`
  through `native_image_args()`, which adds `--accept-stale-images` in the
  stale lanes. The `native-test-images` store is gone (and from the
  sentinel's seed).
- `scripts/run-test-targets.mjs`: the compile-x86 tests and the `heather`
  binary join `PREREQUISITES`' library readers; `lib/lang/lexer` (the
  linked exports) joins what they need built, and the gate builds it first.
- `scripts/test`: an unfiltered run has no native warm-up; the gate's build
  step, four workers, is it. A focused native run builds the three folders'
  closures with `heather check --build-jobs 3 --build-only`.

With a warm gate store, `warm-native --unbuilt` over the same roots now
names only the 28 examples, which each test's child elaborates itself
(`branches`, the largest, 12 s for its first compile on a cloud box).
