---
title: native_linked's export gate fails under load: compiles killed with empty stderr
status: open
labels: [native,testing]
area: infrastructure
created: 2026-11-26
updated: 2026-11-26
---

`crates/cli/tests/native_linked.rs`'s `linked_exports_are_what_the_compiler_emits` has failed under a full `scripts/test --pr` run three times on branch `claude/ownership-checker-sound` (eighth, ninth and tenth sessions) and passed when rerun alone.

## The tenth session's failure, as the test printed it

At c8847a0 (the tree was clean for the run; only `lib/lang/ownership/sound.hthr` was edited while it ran, which no compile here reads), `== suite: 4139 passed, 1 failed, 3 ignored ==`:

```
[done  291/300] crates/cli/tests/native_linked.rs: FAIL (exit=101, 1 failed) (376.93s, 545.1 CPU-s)
---- linked_exports_are_what_the_compiler_emits stdout ----
thread 'linked_exports_are_what_the_compiler_emits' (27744) panicked at crates/cli/tests/native_linked.rs:65:5:
compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::finish:


compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::update:

```

Both failed compiles have **empty stderr**: no rail message, no refusal. While this target ran, the session ran a capped `heather check` of `sound.hthr` beside the suite, and the harness reported that "the kernel killed at least one process for lack of memory" during it. The two compiles were most likely those processes: a kill by the kernel's OOM killer leaves no stderr, and the test prints only stderr.

## What the text says

Not a nondeterminism in the compiler: nothing was emitted that differed from the checked-in assembly; the processes died. It is the machine's shared memory limit, met because the suite's children and another heavy process ran at once.

## To do

- The test should print each failed compile's exit status (signal) beside its stderr, so a kill reads as a kill (`result.status` is in hand at `native_linked.rs:50`).
- Sessions: do not run a whole-file `heather check` beside the native gates (CLAUDE.md's rule to keep editing work light while the suite runs).

## Log

- 2026-11-26: The test now prints each failed compile's exit status beside its stderr (crates/cli/tests/native_linked.rs), so a kill at the shared memory limit reads as a signal. The run that showed it was not a clean one (an edited tree, a whole-file check beside the suite): suite runs are on a clean committed tree with nothing else heavy running.
- 2026-11-26: Reopened by the coordinating session. The exit-status fix (a5405d9) made the failure legible, and the next occurrence confirmed the cause without a second process beside it: on the eleventh soundness session's clean tree, with only the suite running, `Sha256::compress`'s compile was killed (`signal: 9`) and passed alone on the rerun. So the PR lane's own load is enough in a session container: the gate runs four compilers at once beside the library gate. The diagnosis is done; what is open is the cause. Candidates: the gate takes its width from the memory available rather than a constant four; the runner does not start the linked gate beside the library gate; a killed compile is retried once alone before the gate fails. The coordinating session's verification worktree has not shown it in over thirty runs, so the threshold is the container's memory.
