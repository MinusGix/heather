---
title: Master red 2026-11-16 (native_linked.rs, native_utf8.rs)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-16
updated: 2026-11-17
---

Nightly sentinel at accd1145ed0c (`Merge pull request #707 from MinusGix/claude/project-thread-80aop7`),
fresh box, exact images. Last green run: 183b5e7fe46a (#634, 2026-11-15,
`== suite: 4043 passed, 0 failed, 3 ignored ==`); 48 first-parent merges since.

Suite line: `== suite: 4057 passed, 2 failed, 3 ignored ==`
(runner wall time: compile 0s + tests 1366s = 2403s total).

Failing targets:

- `crates/cli/tests/native_linked.rs` (`linked_exports_are_what_the_compiler_emits`)
- `crates/cli/tests/native_utf8.rs` (`utf8_program_exits_as_rust_decides`)

`scripts/sentinel run` did not finish: the session's two-hour background
limit stopped it during the bisect (as on [[master-red-2026-11-14]]), so
`target/sentinel/report.md` was never written and there are no grown-target
or relocation-audit figures, and nothing was published.

## Failures (from `target/sentinel/suite.log`)

```
[done  16/294] crates/cli/tests/native_linked.rs: FAIL (exit=101, 1 failed) (607.42s, 884.9 CPU-s)
  | test linked_exports_are_what_the_compiler_emits ... FAILED <607.383s>
  | failures:
  | ---- linked_exports_are_what_the_compiler_emits stdout ----
  | thread 'linked_exports_are_what_the_compiler_emits' (16298) panicked at crates/cli/tests/native_linked.rs:65:5:
  | compile-x86 lib/native/crypto/sha256_one_block.hthr Sha256::compress:
  | checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-16295-1794819527579033435/sha…
  | stack backtrace:
  |    0: __rustc::rust_begin_unwind
  | … buffered log follows after targets finish
  | process at 68% of its 300 s CPU rail: 205.3 CPU-s, heather compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::finish --symbol
  | process at 68% of its 300 s CPU rail: 202.5 CPU-s, heather compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::update --symbol
```

The buffered log gives the same message in full and nothing after it:

```
thread 'linked_exports_are_what_the_compiler_emits' (16298) panicked at crates/cli/tests/native_linked.rs:65:5:
compile-x86 lib/native/crypto/sha256_one_block.hthr Sha256::compress:
checking the lowering, source agreement, bytes and return certificate in /home/user/heather/crates/cli/../../target/native-linked-16295-1794819527579033435/sha256_compress.certificate.unchecked.hthr

test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 607.39s
```

```
[done  18/294] crates/cli/tests/native_utf8.rs: FAIL (exit=101, 1 failed) (542.42s, 414.3 CPU-s)
  | test utf8_program_exits_as_rust_decides ... FAILED <542.388s>
  | failures:
  | ---- utf8_program_exits_as_rust_decides stdout ----
  | thread 'utf8_program_exits_as_rust_decides' (2069) panicked at crates/cli/tests/native_utf8.rs:147:5:
  | stack backtrace:
  |    0: __rustc::rust_begin_unwind
  |              at /rustc/2d8144b7880597b6e6d3dfd63a9a9efae3f533d3/library/std/src/panicking.rs:689:5
  |    1: core::panicking::panic_fmt
  | … buffered log follows after targets finish
  | process at 98% of its 300 s CPU rail: 293.9 CPU-s, heather write-elf examples/utf8/utf8check.hthr -o /home/user/heather/crates/cli/../../target/native-utf8-program-2068-1…
```

The panic at `native_utf8.rs:147:5` carries an empty message in the buffered
log too (`test result: FAILED. 1 passed; 1 failed; … finished in 542.39s`).

## Bisect: not completed

The sentinel bisects one target at a time over the 48 merges and was stopped
during the third probe of the first target. `native_utf8.rs` was never
bisected.

`crates/cli/tests/native_linked.rs` (probes from `target/sentinel/bisect-*.log`):

| probe | merge | result |
|---|---|---|
| 1 | 3facbe56ded1 (#671) | `== suite: 1 passed, 1 failed, 0 ignored ==` |
| 2 | cd6489a2ec3b (#661) | `== suite: 2 passed, 0 failed, 0 ignored ==` |
| 3 | 039a0a69f6c0 (#669) | stopped while building |

Read at face value that leaves the first failing merge among #662, #660,
#654, #666, #668, #669, #670, #672, #673, #674, #677, #671. It should not be
read at face value: probe 1 was the first probe, and its failure is a
different one from the suite's, with empty messages:

```
thread 'linked_exports_are_what_the_compiler_emits' (14684) panicked at crates/cli/tests/native_linked.rs:65:5:
compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::init:


compile-x86 lib/native/crypto/sha256_stream.hthr Sha256::update:

test result: FAILED. 1 passed; 1 failed; 0 ignored; 0 measured; 0 filtered out; finished in 823.36s
```

`scripts/sentinel` says of this shape: "A failing target with a process at
its rail bisects to whichever merge was probed first over a cold store; check
that the blamed merge can reach the target before trusting it"
([[master-red-2026-11-06]]).

## Rerun at head over the warm stores

After the sentinel stopped, both targets were rerun by hand at accd1145ed0c
in the same container, over the stores the suite and probes had filled
(`scripts/test -p heather-cli --test native_linked --test native_utf8`):

```
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 191.84s
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 122.81s
runner wall time: compile 184s + tests 315s = 512s total
== suite: 4 passed, 0 failed, 0 ignored ==
```

## One cause or several

Both failures are native certificate gates that failed only over the cold
store, each with a `heather` process reported near its 300 s CPU rail (98%
for `write-elf examples/utf8/utf8check.hthr`), and both pass at the same
commit once the stores are warm; the logs do not say which merge raised the
cold cost, and no merge is blamed.

## Log

- 2026-11-17: same target failed again at be464226 with the same shape; see [[master-red-2026-11-17]].
