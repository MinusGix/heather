---
title: Run the library gate once, beside the targets that do not read its store
status: open
labels: [testing, performance, images]
area: infrastructure
created: 2026-10-30
updated: 2026-10-30
---

The 2026-10-30 fresh-box profile of an unfiltered `scripts/test` (master
c46cebd, raw data in the project's `suite-profile-2026-10-30/`) found its
largest single cost before any test ran: `cli_images_warmup`, the library
gate run alone so that `native_cat.rs`/`native_tools.rs`'s `write-elf` would
find the world's images built, took 874 s of wall at about 1.6 of 4 CPUs.
The parallel phase then ran the same gate again as a test, warm (about 291
CPU-s, 180 s).

## Why the gate leaves cores idle

Measured on a 4-CPU cloud box, the suite's dev binary, the sentinel seed of
c16d0e3 restored before each run, the gate alone (`cargo test -p heather-cli
--test library -- --exact every_library_module_checks`), CPU busy sampled
every 5 s:

| kernel width per child | wall | CPU (user+sys) | mean CPUs busy | peak RSS, all children |
|---|---|---|---|---|
| 1 (as the suite runs it) | 871 s | 1372 s | 1.64 | 2.6 GB |
| 1, repeated | 596 s | 943 s | 1.63 | 2.6 GB |
| 2 | 611 s | 1116 s | 2.03 | 5.1 GB |
| 4 | 736 s | 1451 s | 2.03 | 6.1 GB |

The two width-one runs did identical work and differ by 45% in CPU: this
box's speed drifts that much within an hour, so seconds compare only within
a row's own ratios. What is stable is the parallelism.

The gate is a **chain**. A module's image is keyed by every module loaded
before it in its process (`docs/archive/library-world-design.md` §1), so world
module *k* can only be built over modules 0..k-1, and every child that
needs it waits on its build lock. Whatever the three children do, the
world's shared modules are elaborated one after another; the children only
add the folder-local modules (`lib/_tests` probes, leaves) beside the chain.
The per-folder lines the gate now prints (`gate folder <dir> <start> <end>`,
with `--nocapture`) show the chain: `lib/std/tactic` and
`lib/_tests/std/tactic` span most of the run, then `lib/native` and
`lib/_tests/native` finish it with two children busy.

A wider kernel gate pipelines each child's kernel checks against its
elaborator and raises the mean to about two CPUs, at roughly twice the
memory. It is not adopted: the gain is a quarter of the wall at best,
the per-child CPU it costs under the 300 s rail is unmeasured on a box this
noisy, and the change below already gives the idle CPUs to other targets.

## Change

- `scripts/run-test-targets.mjs` knows **prerequisites**
  (`PREREQUISITES`): the library gate starts first, `native_cat` and
  `native_tools` wait until it has finished (pass or fail), and every other
  target fills the slots the gate leaves idle. A prerequisite the run does
  not hold (the pr lane's selection) blocks nothing.
- `scripts/test` no longer runs `cli_images_warmup` before an unfiltered
  run, so the gate runs once, as the test. Focused runs of a native target
  still warm it first.

Nothing the gate checks moved: the same test, the same binary, the same
store, the same rails per child. The verdicts are the gate's own run, not a
reuse of an earlier one.

## Left

- The chain itself. Making a module's image independent of modules it does
  not import ([[nominal-tags-from-declaration-identity]], and observing only
  the closure, `docs/archive/library-world-design.md` §4) would let the world build
  as a DAG instead of a line, which is where the gate's wall really goes.
- `native_warmup` (`the_bundled_library_checks`, about 85 s on one CPU)
  still runs alone before the parallel phase; it could become a prerequisite
  of the `heather` bin target in the same way, run in its own process and
  skipped in the target's run.

## Log

- 2026-10-30: filed with the change above (the gate measurements in the
  table; the suite measurement is in the PR).
- 2026-10-30: One unfiltered `scripts/test` from the same seed with the
  change: green, 3635 passed (the profile's count). Warmups 69 s, test phase
  985 s, against the profile's 1001 s of warmups and 946 s of tests. The gate
  ran 676 s / 1018 CPU-s beside the other targets, and all of them had
  finished when it did; the tail is now the gate followed by `native_tools`
  (303 s), so the chain is the next lever.
- 2026-10-30: The world chain is gone ([[module-dag-build]], `docs/infrastructure/module-dag-design.md`): images are keyed by import closures, so the children build independent modules in parallel; cold gate wall drops by about half, peak memory rises by about a third.
- 2026-11-05: gardener: cites a file it shares with [[early-cutoff-registry-and-order-granularity]] (`docs/archive/library-world-design.md`).
