---
title: Master red 2026-11-21 (lib_std_int.rs)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-21
updated: 2026-11-21
---

Nightly sentinel at 714a3ecb (`Merge pull request #834 from MinusGix/claude/runtime-several-words`),
fresh box, exact images. Last green run: d08e177a67f3.

Suite line: `== suite: 4106 passed, 1 failed, 3 ignored ==` in 1292 s.

Failing targets:

- `crates/elab/tests/lib_std_int.rs` (`lib_std_int::the_kernel_required_motives_are_retained`)

## Failure (from `target/sentinel/suite.log`)

```
[done  116/299] crates/elab/tests/lib_std_int.rs: FAIL (exit=101, 1 failed) (2.23s, 2.1 CPU-s)
test lib_std_int::the_kernel_required_motives_are_retained ... FAILED <2.217s>

failures:

---- lib_std_int::the_kernel_required_motives_are_retained stdout ----

thread 'lib_std_int::the_kernel_required_motives_are_retained' (3874) panicked at crates/elab/tests/families/../lib_std_int.rs:56:5:
a motive whose omission elaborates but fails the local kernel check is retained
stack backtrace:
   0: __rustc::rust_begin_unwind
   1: core::panicking::panic_fmt
   2: family_library::lib_std_int::the_kernel_required_motives_are_retained
             at ./crates/elab/tests/families/../lib_std_int.rs:56:5
   3: family_library::lib_std_int::the_kernel_required_motives_are_retained::{closure#0}
             at ./crates/elab/tests/families/../lib_std_int.rs:48:46

failures:
    lib_std_int::the_kernel_required_motives_are_retained

test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 225 filtered out; finished in 2.22s
```

The assertion at `crates/elab/tests/lib_std_int.rs:56` is the second one:
elaborating the `int` module now emits a `Lint::RedundantMatchMotive`
warning (the test's first assertion, that the three explicit
`decide_bit_split` motives are still in `lib/std/int`, passed).

## Bisect

First failing merge since the last green run (d08e177a67f3):

- `crates/elab/tests/lib_std_int.rs`: 2cc92754f Merge pull request #833 from
  MinusGix/claude/runtime-admits-enum-only (`target/sentinel/bisect-2cc92754fede.log`
  reproduces the same panic; its parent 685a01de8 (#831) was checked too).

## Relocation audit

The report also says: "Relocation audit from d08e177a67f3: a library check
failed". `target/sentinel/relocation-audit/check.log` is one line:

```
error: module `bool` is in two search directories (`lib/std/core/bool.hthr`, `/home/user/heather/target/sentinel/relocation-audit/old/lib/std/core/bool.hthr`) — that is an error, not a precedence: remove one copy or drop one `-L`
```

That is the audit's own invocation refusing duplicate search directories,
not a library module failing.

One cause: a single failing test, bisected to one merge (#833); the
relocation-audit line is a separate sentinel-tooling error.

## Log

- 2026-11-21: filed by the nightly sentinel.
