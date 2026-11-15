---
title: Build the native folders' closures first in the gate's build step, so the native gates start earlier
status: closed
labels: [testing,performance,native,images]
area: infrastructure
created: 2026-10-31
updated: 2026-10-31
---

This round started as "split the longest `lib/native` modules": the
belief was that they were the cold gate's critical path and over the
300 s budget. A measurement on master f9c6e9d says neither holds any more.
Since #291 every module builds in a process of its own
(`docs/infrastructure/module-dag-design.md` §12), so the 300 s rail is per module, and the
`lib/native` folder child only replays (3 s over a built store).

## Measured

`heather check --cache --expectations --build-jobs 4 --build-only lib`,
the gate's build step, on a fresh store, a 4-CPU cloud box, the dev
binary, `HEATHER_KERNEL_WORKERS=1`, `ulimit -v 6291456 -t 300`, with the
new `--build-times`:

| | before | `--build-first lib/native lib/_tests/native` |
|---|---|---|
| step wall | 221 s | 224 s |
| summed module wall | 824 s | 814 s |
| last native-folder module built | 199.5 s | 98.7 s |

- The step is CPU-bound: 824 s over four jobs is a floor of about 206 s.
- The chain that ended last was creal → creal_interval → interval_tactic →
  `interval_tactic_real_tests` (50 s, the largest module), which waited
  45 s for a job.
- The native chain, `native_compile` → … → `native_compile_structured` →
  `native_compile_correct`, was done by 89 s. The largest native modules
  were `native_compile_correct` 11.9 s, `native_compile_args` 11.7,
  `function_ir_lower_calls` 10.9, `native_compile_structured` 10.7 and
  `native_build_parts` 10.7.
- Before the change, native modules were ready at about 100 s but started
  between 130 and 195 s. Their chains in source bytes are shorter than the
  std test chains' (`x86_64_asm_table`, under `native_compile_elf`, was
  ready at 18.6 s and started at 92.8 s). So the runner's probe from
  [[native-gates-start-when-their-images-exist]] could release the native
  gates only near the end of the step.

## What changed

- `heather check --build-times <file.tsv>` writes a row per module the
  build step built: `ready_s`, `start_s`, `end_s`, `wall_s`, `readied_by`.
- `heather check --build-first <dir>` (repeatable) starts the modules below
  each directory, and their closures, before any other ready module.
- The library gate passes `--build-first lib/native --build-first
  lib/_tests/native`, the runner's `PREREQUISITES` `built` folders.

Splitting modules was not done. The step has no chain to shorten, and
every new module adds a replay of its closure to the step's CPU.

## Left

- Whether the earlier release moves a whole suite run's tail depends on a
  runner slot being free for `native_tools` (see the issue above). It was
  not measured here.
- Ordering by source bytes is a weak stand-in for time. The largest test
  modules (`interval_tactic_real_tests`, `cast_tests`) are where the
  step's tail is. Ordering by the previous run's `--build-times` would
  rank them better.

## Log

- 2026-10-31: Filed and closed in one round (this file).
