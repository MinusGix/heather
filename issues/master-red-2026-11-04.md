---
title: Master red 2026-11-04 (library, native_cat, native_tools; incomplete)
status: open
labels: [testing, sentinel]
area: infrastructure
created: 2026-11-04
updated: 2026-11-04
---

Nightly master sentinel at `c345c863e7dd` (#414), exit 2 (incomplete).

`== suite: INCOMPLETE (3743 passed before death, 22 failed) ==` in 6675 s
(fresh box, exact images). The run header reports
`automatic bound: memory 4, CPU 3; reserving 2.0 GiB for the host`.

Failing targets (from `target/sentinel/report.md`):

- `crates/cli/tests/library.rs` (exit=101, 1 failed, 2955.76s)
- `crates/cli/tests/native_cat.rs` (exit=101, 8 failed, 2404.36s)
- `crates/cli/tests/native_tools.rs` (exit=101, 13 failed, 3394.38s)

Also in `suite.log` (the cause of INCOMPLETE; not listed as failing targets):

- `crates/elab/tests/showcase_calculator.rs`: TERMINATED (signal=SIGKILL) (525.00s)
- `crates/elab/tests/parser_library.rs`: TERMINATED (signal=SIGKILL) (601.06s)

## Bisect

None. The report says: "The last green run (a24a2b32a520) is not an ancestor
of this commit; no bisect." (origin/master was force-updated, `f9c6e9d...c345c86`.)
The relocation audit also reports: "a library check failed
(`target/sentinel/relocation-audit/check.log`)"; that file does not exist after the run.

## Failure excerpts (`target/sentinel/suite.log`)

### crates/cli/tests/library.rs
```
[done  273/276] crates/cli/tests/library.rs: FAIL (exit=101, 1 failed) (2955.76s, 7417.6 CPU-s)
  | test every_library_module_checks ... FAILED <2955.743s>
  | failures:
  | ---- every_library_module_checks stdout ----
  | build: native_build_parts (signal: 9 (SIGKILL)):
  | build: native_compile_correct (signal: 9 (SIGKILL)):
  | build: 277 modules built ahead, 2 failed
  | gate folder	lib/std/relation	0.0	0.3

gate folder	lib/native	120.0	672.7

thread 'every_library_module_checks' (10525) panicked at crates/cli/tests/library.rs:301:5:
the library does not check:
== lib/_tests/native (signal: 9 (SIGKILL))
warning: consecutive calls to the same function can use one argument list; write `f(a, b)` instead of `f(a)(b)`
  --> /home/user/heather/lib/native/function_ir/function_ir.hthr:1021:23
```
Also `== lib/native (signal: 9 (SIGKILL))` at suite.log line 1781.

### crates/cli/tests/native_cat.rs
```
[done  274/276] crates/cli/tests/native_cat.rs: FAIL (exit=101, 8 failed) (2404.36s, 2403.1 CPU-s)
  | test compiled_cat_runs_as_cat ... FAILED <304.136s>
  | test larger_program_runs_as_cat has been running for over 60 seconds
  | test every_written_program_gets_its_theorem ... FAILED <526.192s>
  | test mebibyte_buffer_runs_as_cat has been running for over 60 seconds
  | test larger_program_runs_as_cat ... FAILED <613.823s>
  | test procedures_run has been running for over 60 seconds
  | test mebibyte_buffer_runs_as_cat ... FAILED <622.222s>
  | test refused_programs_name_their_reason has been running for over 60 seconds
thread 'compiled_cat_runs_as_cat' (4752) panicked at crates/cli/tests/native_cat.rs:24:5:

stack backtrace:
```
Panic sites with empty messages: `native_cat.rs:24` (`write_cat`), 106, 129, 172, 195, 226, 247, 284.

### crates/cli/tests/native_tools.rs
```
[done  275/276] crates/cli/tests/native_tools.rs: FAIL (exit=101, 13 failed) (3394.38s, 3946.8 CPU-s)
  | test compiled_decimals_round_trip_the_widest_words ... FAILED <607.280s>
  | test compiled_echo_runs_as_gnu_echo has been running for over 60 seconds
  | test compiled_cat_files_runs_as_gnu_cat ... FAILED <686.662s>
  | test compiled_grep_f_runs_as_gnu_grep has been running for over 60 seconds
  | test compiled_echo_runs_as_gnu_echo ... FAILED <647.560s>
  | test compiled_head_runs_as_gnu_head has been running for over 60 seconds
  | test compiled_grep_f_runs_as_gnu_grep ... FAILED <664.235s>
  | test compiled_head_takes_its_count_as_gnu_head has been running for over 60 seconds
thread 'compiled_decimals_round_trip_the_widest_words' (4757) panicked at crates/cli/tests/native_tools.rs:44:5:

stack backtrace:
```
Panic site with empty message: `native_tools.rs:44` (`write_program`), also from `compiled_cat_files_runs_as_gnu_cat` and `compiled_echo_runs_as_gnu_echo`.

## Cause

All five failing or terminated targets involve a SIGKILL (signal 9): the two
elab targets were killed outright, and the library gate's `lib/native` and
`lib/_tests/native` checks and `native_build_parts` / `native_compile_correct`
builds died with signal 9. The native_cat/native_tools panics carry no message in
the log. The log does not say who sent the signal, so this looks like one cause
(killed children), but that is not established; a rerun is needed to tell a
resource kill from a regression.
