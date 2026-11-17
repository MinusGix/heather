---
title: Master red 2026-11-17 (native_linked.rs)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-17
updated: 2026-11-17
---

Nightly sentinel at be464226 (`Merge pull request #746 from MinusGix/claude/project-thread-eg2kpd`),
fresh box, exact images. Last green run on record: 183b5e7f (#634, as in
[[master-red-2026-11-16]]); 93 first-parent merges since.

Suite line: `== suite: 4074 passed, 1 failed, 3 ignored ==`
(runner wall time: compile 0s + tests 1543s = 2560s total).

Failing targets:

- `crates/cli/tests/native_linked.rs` (`linked_exports_are_what_the_compiler_emits`)

`scripts/sentinel run` did not finish: the session's two-hour background
limit stopped it during the bisect (as on [[master-red-2026-11-14]] and
[[master-red-2026-11-16]]), so `target/sentinel/report.md` was never written:
there are no grown-target or relocation-audit figures, and nothing was
published.

## Failure (from `target/sentinel/suite.log`)

```
[done  21/296] crates/cli/tests/native_linked.rs: FAIL (exit=101, 1 failed) (837.62s, 1204.5 CPU-s)
  | test linked_exports_are_what_the_compiler_emits ... FAILED <837.595s>
  | failures:
  | ---- linked_exports_are_what_the_compiler_emits stdout ----
  | thread 'linked_exports_are_what_the_compiler_emits' (15899) panicked at crates/cli/tests/native_linked.rs:65:5:
  | compile-x86 lib/native/crypto/sha256_one_block.hthr Sha256::compress:
  | checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-15898-1794905922494377609/sha…
  | compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::finish:
  | checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-15898-1794905922494377609/sha…
  | … buffered log follows after targets finish
  | process at 95% of its 300 s CPU rail: 283.7 CPU-s, heather compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::update --symbol
  | process at 75% of its 300 s CPU rail: 226.1 CPU-s, heather compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::finish --symbol
  | process at 75% of its 300 s CPU rail: 223.9 CPU-s, heather compile-x86 lib/native/crypto/sha256_one_block.hthr Sha256::compress --symbol
```

The buffered log gives the same two messages in full and nothing after them:

```
thread 'linked_exports_are_what_the_compiler_emits' (15899) panicked at crates/cli/tests/native_linked.rs:65:5:
compile-x86 lib/native/crypto/sha256_one_block.hthr Sha256::compress:
checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-15898-1794905922494377609/sha256_compress.certificate.unchecked.hthr


compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::finish:
checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-15898-1794905922494377609/sha256_finish.certificate.unchecked.hthr

test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 837.61s
```

## Bisect: not completed

Over the 93 merges since 183b5e7f (probes from `target/sentinel/bisect-*.log`):

| probe | merge (position) | result |
|---|---|---|
| 1 | 3938066b2c9a (#685, 47/93) | `== suite: 2 passed, 0 failed, 0 ignored ==` (267.09s) |
| 2 | c18ad6f516dc (#719, 70/93) | `== suite: 2 passed, 0 failed, 0 ignored ==` (288.97s) |
| 3 | 72a6d583b3da (#729, 82/93) | `== suite: 2 passed, 0 failed, 0 ignored ==` (287.96s) |
| 4 | 83c35ade732e (#725, 88/93) | stopped while building |

Read at face value, the first failing merge is among the last eleven:
#725 and the merges after #729 up to head (#713, #743, #720, #728, #746,
and those between). It should not be read at face value: every probe ran
over the store the suite had filled, and the first probe passed at
#685 — so the target passed over a warm store at a commit 46 merges before
head, while the suite's cold-store run failed with three `compile-x86`
processes at 75–95% of their 300 s CPU rail. `scripts/sentinel` warns that
a failing target with a process at its rail bisects unreliably over the
store ([[master-red-2026-11-06]]). No merge is blamed.

## One cause or several

One target, and it is the same failure shape as
[[master-red-2026-11-16]] (`linked_exports_are_what_the_compiler_emits`
failing on `Sha256::compress` certificate checking over a cold store, with
SHA-256 `compile-x86` processes near the 300 s CPU rail), which looks like
one cause carried over rather than a new regression; the logs do not say
which merge raised the cold cost.
