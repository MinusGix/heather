---
title: Master red 2026-11-03 (native_tools compiled_sort)
status: closed
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-03
updated: 2026-11-04
---

Nightly sentinel at `b0379188b742` (origin/master head when the run started):

`== suite: 3738 passed, 1 failed, 2 ignored ==` in 2798 s (fresh box, exact images).

Failing target: `crates/cli/tests/native_tools.rs`
(`[done  272/273] ... FAIL (exit=101, 1 failed) (1796.29s, 2715.9 CPU-s)`).

## Failure (from `target/sentinel/suite.log`)

```
test compiled_sort_runs_as_gnu_sort ... FAILED <305.383s>
---- compiled_sort_runs_as_gnu_sort stdout ----
thread 'compiled_sort_runs_as_gnu_sort' panicked at crates/cli/tests/native_tools.rs:44:5:
checking `sort_tool`'s compile and its 12893 bytes in /home/user/heather/target/native-sort-16183-1793697075251961474/sort.certificate.unchecked.hthr
```

Line 44 is the first `assert!` after `write-elf`: the command did not succeed, and its
stderr is the "checking ... compile" message above (the `.unchecked.hthr` certificate was
left behind). The other 13 tests in the target passed.

## Bisect

None. The report says: "The last green run (a24a2b32a520) is not an ancestor of this
commit; no bisect." (`git` also reported `Not a valid commit name a24a2b32a520...`.)

## Relocation audit

"Relocation audit from a24a2b32a520: a library check failed
(`target/sentinel/relocation-audit/check.log`)." That log does not exist in the container
(the audit's baseline commit was missing, `fatal: not a tree object`), so this is likely
an artifact of the unreachable baseline rather than a library failure; not verified.

## Cause

A single failing test, so one failure; its cause is not established from the logs
(the log only shows the certificate check for `sort_tool` taking ~305 s and failing).

## Log

**2026-11-04.** Same cause as [[master-red-2026-11-04]]: `sort_tool`'s
`write-elf` costs 320–350 CPU-s over warm images at both `b037918` and
`4c1b702`, against the 300 s rail. native_tools now runs under a 900 s rail;
the cost itself stays with [[native-sort-gate-rail]].
