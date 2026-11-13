---
title: Audit the function certificate for statements that are one evaluation of the whole program
status: open
labels: [native,certificates,scaling]
area: heather-in-heather
milestone: [nh-library]
created: 2026-11-12
updated: 2026-11-12
---

A `compile-x86` certificate proves some of its facts by one kernel evaluation over the whole program or the whole code. Two of them ran out of the kernel's fuel as programs grew and were restated a function at a time: `{prefix}_evaluable` ([[function-ir-evaluable-quadratic]]) and `{prefix}_quiet` (2026-11-12, with the scanner's automaton under `scan_token`; `program_quiet_drop`, `function_ir_writes.hthr`). Each was found by an export failing, not before.

Still one evaluation each in `crates/cli/src/native/verified.rs`:

- `{prefix}_holes` (`code.no_holes()`), `{prefix}_reads` (`code.blocks_read_own()`), `{prefix}_laid` (`code.laid_out()`): walks of all the emitted code.
- `{prefix}_entry_at`: the label map of all the code, applied at one label.
- `{prefix}_lowers`: assembled from per-function `_emits_k`, so already in parts ([[native-function-emission-in-parts]] owns what is left there).

SHA-256's compression is the next program several times the automaton's size ([[sha2-compress-native]]).

## What to do

- Measure each statement's `eval_steps` on `scan_token`'s certificate (`--only <theorem> --timings`, CLAUDE.md) and see which grow faster than the code.
- Give each walk over code a `drop` lemma of the same shape as `program_quiet_drop` (a head check and the rest), or state it per function beside `_emits_k`, where the code of one function is already a literal.
- Add a control: an export in `native_linked.rs` large enough that a whole-program statement would not fit, so the next one is found by a test.

## Done when

No statement of the certificate is one evaluation whose cost grows with the whole program, or each that remains is listed here with its measured slope and why it is safe.
