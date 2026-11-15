---
title: Master red 2026-11-14 (library.rs, when_tests)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-14
updated: 2026-11-14
---

Nightly sentinel at a274632ca022 (`Merge pull request #615 from MinusGix/claude/project-thread-ks488q`),
fresh box, exact images.

Suite line: `== suite: 4031 passed, 1 failed, 3 ignored ==`
(runner wall time: compile 0s + tests 1599s = 3525s total).

Failing target: `crates/cli/tests/library.rs` (`every_library_module_checks`).

`scripts/sentinel run` did not finish: the session's two-hour background
limit stopped it during the bisect, so `target/sentinel/report.md` was never
written and there are no grown-target or relocation-audit figures. The suite
log and two bisect probes are the sentinel's; the last two probes were run by
hand with the same command (`scripts/test -p heather-cli --test library`).

## Failure (from `target/sentinel/suite.log`)

```
[done  287/290] crates/cli/tests/library.rs: FAIL (exit=101, 1 failed) (1456.66s, 3655.2 CPU-s)
  | test every_library_module_checks ... FAILED <1456.631s>
  | failures:
  | ---- every_library_module_checks stdout ----
  | build: when_tests (exit status: 1):
  | build: 531 modules built ahead, 1 failed
  | gate folder	lib/std/core	0.0	0.6
  | gate folder	lib/std/relation	0.0	1.1
  | gate folder	lib/_tests/std/relation	0.0	1.1
  | … buffered log follows after targets finish
  | process at 91% of its 300 s CPU rail: 272.1 CPU-s, heather check --cache-dir /home/user/heather/target/cli-check-images --expectations
  | process at 72% of its 300 s CPU rail: 215.9 CPU-s, heather check --cache-dir /home/user/heather/target/cli-check-images --expectations
  | process at 69% of its 300 s CPU rail: 208.0 CPU-s, heather check --cache-dir /home/user/heather/target/cli-check-images --expectations
```

The one module that failed, under `== lib/_tests/std/core (exit status: 1)`:

```
error: a `When` is wanted here, so this call of `at` tests its condition `∥nat::Nat::Lt(bitvec::BitVec::toNat(i), n)∥`, which has no decision (`Decide<∥nat::Nat::Lt(bitvec::BitVec::toNat(i), n)∥>`) here: give `inside := …` and take the value, or call a function whose own work decides it and returns a `When` (docs/language/when-design.md §3)
  --> lib/_tests/std/core/when_tests.hthr:26:89
   |
26 | fn word_at({w, n: Nat}, v: [BitVec(w); n], i: u64) → When<BitVec(w), i.toNat() < n> { v.at(i) }
   |                                                                                       ^^^^^^^

error: unbound name `option`
  --> lib/_tests/std/core/when_tests.hthr:31:27
   |
31 | theorem word_at_inside(): word_at(three(), 1).option() = Some(20) { refl }
   |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

error: unbound name `option`
  --> lib/_tests/std/core/when_tests.hthr:32:28
   |
32 | theorem word_at_outside(): word_at(three(), 3).option() = None { refl }
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

error: unbound name `is_present`
  --> lib/_tests/std/core/when_tests.hthr:33:35
```

The remaining errors are `unbound name` for `val`, `option`, `is_present`,
`word_at` (56:11, 60:11), `word_or_zero` (63:29), `word_again` (64:27), and
two directives refused "not as `expect-error(kernel)` says" (214:33, unbound
`option`) and "not as `expect-error(mismatch)` says" (218:47, unbound `val`).
Total: `lib/_tests/std/core/when_tests.hthr: 14 errors`. The panic is
`crates/cli/tests/library.rs:303:5`.

## Bisect

First-parent merges probed with `crates/cli/tests/library.rs` alone:

| merge | PR | result |
|---|---|---|
| a39d1943 | #605 | `== suite: 4 passed, 0 failed, 0 ignored ==` (sentinel) |
| fa62495d | #616 | `== suite: 4 passed, 0 failed, 0 ignored ==` (sentinel) |
| 53a29d69 | #612 | `== suite: 4 passed, 0 failed, 0 ignored ==` (by hand) |
| 7d3ba710 | #614 | `== suite: 3 passed, 1 failed, 0 ignored ==` (by hand), same first error at `when_tests.hthr:26:89` |
| a274632c | #615 | failing (the suite run above) |

First failing merge: **7d3ba710, `Merge pull request #614 from
MinusGix/claude/project-thread-xrvrgu`**; its first parent 53a29d69 (#612) is
green. #612 is the last merge before it that touches
`lib/_tests/std/core/when_tests.hthr`; #614's diff from #612 does not touch
that file and does touch `crates/elab/src/checking.rs` and
`crates/elab/src/measure_context.rs`.

## Cause

One failing target and one failing module, whose thirteen later errors name
declarations that depend on the first (`word_at`), so this looks like one
cause. I have not read a cause in the logs beyond the first error's text.

Master has moved since the run (nine more merges, through a7075dc9 / #628),
and `lib/_tests/std/core/when_tests.hthr` changed in that range; this run
says nothing about whether the newer head is still red.
