---
title: The elab tests' wc fixture duplicates examples/x86-native/wc.hthr
status: closed
labels: [tests, native]
code: crates/elab/tests/function_ir_loop_trace.rs @ 357c0afa
created: 2026-09-29
updated: 2026-09-29
---

`WC_SOURCE` (crates/elab/tests/function_ir_loop_trace.rs) and the
`wc_body_folds` in `WC_PROCESS` (read_state_process.rs) are copies of the
step, its advance theorem and its folds theorem from
`examples/x86-native/wc.hthr`, written before the program existed (slices
B–C of [[native-wc]]). A change to the program's step is not seen by
read_state_process, read_fields_process or the loop-trace tests.

Fix: `include_str!` the example as the `wc_loop` module. It imports
`omega` and `bitvec_omega`, which the harness has; the fixture's name
`wc_loop` and the examples' `wc` differ, so the qualified names in the
three test modules change with it.

## Log

- 2026-09-29: Fixed: `WC_SOURCE` is `include_str!` of `examples/x86-native/wc.hthr`, checked as
  module `wc` (the loop-trace test adds `omega` and `bitvec_omega` to its harness,
  read_state_process adds `bitvec_omega`). One helper, `wc_record_loop`, elaborates
  it and generates the record loop for all three test modules, and WC_PROCESS's
  copy of `wc_body_folds` is gone — the program's own theorem is passed, as the
  CLI's `--folds` does. One collision: the test's generator prefix is `wc`, so
  the generated `wc_bytes()` (the loop's code) and the program's `wc_bytes` spec
  share a name; the client modules list `import wc_native::{wc_bytes};`. The CLI
  build is not affected (its prefix is `count_wc_native`).
