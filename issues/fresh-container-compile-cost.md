---
title: A fresh container's compile built every integration-test binary at opt-level 3
status: closed
labels: [testing,performance,build]
area: infrastructure
created: 2026-10-22
updated: 2026-10-22
---

The top remaining item of [[suite-full-lane-cost-2026-10]]: a fresh 4-CPU
cloud container paid ~5 minutes of `cargo test --workspace --no-run` before
the first test ran. That issue read the critical path as the two O3 compiles
of elab's sources (the lib and `heather-elab-unit`) and found no cheap lever.

## What the timeline showed

`cargo --timings`, cold, master b04c174, 4 CPUs: 267 s wall (279 s and 1022
CPU-s in a second cold run under `time`). After the elab lib (14 → 177 s),
the last 90 s were elab's 16 integration-test binaries (`family_*` and the
three standalone targets), 10–24 s each. They compiled at **opt-level 3**:
`[profile.dev.package.heather-elab]` applies to every target of the package,
tests included (the rustc command lines say `-C opt-level=3`), and a profile
override cannot name one target. `[profile.test.package.…]` is no way out:
under `cargo test` it also rebuilds the library at the test profile.

Compiling one family binary by hand from cargo's own command line,
`family_function_ir`: O3 25 CPU-s, O1 15, O0 2.8. The kernel's ~25
integration-test binaries were the same story (`eval_differential`: O3 7.7
CPU-s, O0 1.4) on the window where the elab unit-test compile waited for
CPUs. The test code only drives the libraries; the hot code is the library,
which stays optimized. Running `eval_differential` with O0 test code: 0.46 →
0.58 s.

## The change

The libraries move into packages of their own, so the opt-level can differ:

- `heather-kernel-lib` (`crates/kernel-lib/Cargo.toml`) and `heather-elab-lib`
  (`crates/elab-lib/Cargo.toml`) build the lib from `crates/kernel/src` and
  `crates/elab/src`, keep the crate names `heather_kernel`/`heather_elab`, and
  carry the opt-level 3 overrides. The kernel's unit tests run there
  (`-p heather-kernel-lib --lib`); elab's stay in `heather-elab-unit`.
- `heather-kernel` and `heather-elab` keep their integration tests and benches
  (`autolib = false`) and forward their features. So `-p heather-elab --test X`,
  `-p heather-kernel --test X`, the bench scripts and every test path are
  unchanged; the dependents' manifests name the `-lib` packages.
- The runner strips a `-lib` suffix from package labels so the kernel's unit
  tests keep their timing-history label `heather-kernel (crates/kernel/src/lib.rs)`.

Benches use the bench profile (release), which has no per-package overrides,
so they are unaffected.

## Result

Same box, cold target directory, `time cargo test --workspace --no-run`:

| | wall | CPU (user+sys) |
|---|---|---|
| master | 279 s | 1022 s |
| elab split only | 227 s | 830 s |
| elab + kernel split | 216 s | 786 s |

The build is now CPU-bound (786 / 4 ≈ 197 s floor). The tail is
`heather-elab-unit`'s O3 compile (~210 CPU-s, a duplicate of the lib's by
construction), which Cargo schedules late because nothing depends on it.

The tests do not pay it back. Full `scripts/test` on the same box, both
with cold image and verdict stores: master tests 716 s / 2228 CPU-s, after
660 s / 2090 CPU-s, same 3623 passed and the same set of target labels. The
kernel's integration tests sum 15.2 → 17.3 CPU-s with O0 test code; no
target moved by more than a few seconds except two that share prefix images
with others (which one builds them first varies). Both runs lost
`linux_wp.rs` to the 300 CPU-s rail: on a cold image store it dies on master
too, and warm it passes in 193 s on both, so that is not this change
([[linux-wp-cold-rail]]).

A member-file edit now rebuilds its family binary at O0 as well, which
[[elab-rebuild-floor]]'s loop pays per test edit.

Ruled out on the way:

- `heather-elab-unit` at a lower opt-level. O0 fails two module-image tests
  that assert the decoder's stack frames fit an O3 budget
  (`every_nesting_level_fits_the_decoders_frame_bound`,
  `the_depth_budget_holds_on_a_small_callers_stack`), and O1 saves only ~40
  CPU-s while testing frames the shipped build does not have. Kept at O3.
- The environment's setup script runs at every session start, so it cannot
  carry a prebuilt `target/` between containers.

## Log

- 2026-10-22: Filed and closed with the package split above. Cold compile
  279 → 216 s, CPU 1022 → 786 s.
