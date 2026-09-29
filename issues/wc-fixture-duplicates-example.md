---
title: The elab tests' wc fixture duplicates examples/x86-native/wc.hthr
status: open
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
