---
title: Master red 2026-11-06 (native_branches)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-06
updated: 2026-11-06
---

Nightly sentinel at 6aa060a64146 (`grind: constructor facts, disequalities and side reducts (round 3) (#432)`).

Suite line: `== suite: INCOMPLETE (3773 passed before death, 1 failed) ==`
(runner wall time: compile 1s + tests 2937s = 3174s total; fresh box, exact images).

Failing target: `crates/cli/tests/native_branches.rs`
(`source_nested_conditionals_execute`).

## Failure (from `target/sentinel/suite.log`)

```
[done  7/276] crates/cli/tests/native_branches.rs: FAIL (exit=101, 1 failed) (480.91s, 298.6 CPU-s)
  | test source_nested_conditionals_execute ... FAILED <480.882s>
  | thread 'source_nested_conditionals_execute' (10672) panicked at crates/cli/tests/native_branches.rs:16:9:
```

The panic is the `assert!(result.status.success(), "{stderr}")` after
`compile-x86`; the logged message is empty (no stderr text). The log's
"slowest test targets" table lists this target at 480.89s and 298.6 CPU-s
(100% of the CPU rail), the same run's `targets past 50% of the CPU rail`
section. I have not read a cause beyond that.

## Bisect (from `target/sentinel/report.md`)

First failing merge since the last green run (c374f3f0db91):

- `crates/cli/tests/native_branches.rs`: 9406e04e Merge pull request #430 from MinusGix/atelier/tracker-gardener-303b5z

Relocation audit from c374f3f0db91: a library check failed
(`target/sentinel/relocation-audit/check.log`), which reads:
`error: module `bool` is in two search directories (`lib/std/core/bool.hthr`, `.../target/sentinel/relocation-audit/old/lib/std/core/bool.hthr`) — that is an error, not a precedence: remove one copy or drop one `-L``.
This looks like an audit-harness error rather than a library result.

## Cause

One failing target, so one apparent cause; the logs name no cause beyond the
failed `compile-x86` invocation and the CPU-rail figure above.
The "INCOMPLETE" status was reported with only one failure; no further target death is named in the log.

## Log

**2026-11-06.** Cause measured: a cold store, not a regression of #430.
#429 made every function in `examples/x86-native/branches.hthr` but three a
`runtime fn`, which needs the module to import `tactic`, `char`, `string`,
`rt`, `rt_lower`, `function_ir`, `function_ir_eval` and `runtime`
([[runtime-generator-imports]]); #431 grew `runtime.hthr` again. The test's
nine `compile-x86` children share the `native-test-images` store, and
`scripts/test`'s `native_warmup` warms only the bundled proof library in it,
so on a fresh store the first child elaborates that whole closure under its
own 300 s rail. Cloud box, dev binary, width one, an empty `--cache-dir`:
`compile-x86 … nested_true` costs 364 CPU-s (359 user + 5 sys) and passes
under a loosened rail; `nested_false` right after it, over the store the
first one wrote, costs 43 CPU-s. (The empty store also lacked the bundled
prefix the suite's warmup provides, so the suite's first child pays less
than 364, but on the sentinel's box it reached the rail.)

The bisect's blame on #430 is an ordering artefact: its first probe (#430)
ran cold and died, writing images of the same `lib/` that #429 has, so the
second probe (#429) replayed them and passed. A rail kill bisects to
whichever merge is probed first over a cold store.

The PR lane did not skip this: #429 and #431 touch `lib/native`, so every
native gate ran on them, but over stores their own rounds had already warmed.
