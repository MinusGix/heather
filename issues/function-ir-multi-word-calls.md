---
title: FunctionIR calls with several argument and result words at their widths
status: open
labels: [native,function-ir,compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-11-21
---

FunctionIR's `Call` region (`lib/native/function_ir/function_ir.hthr`) takes
64-bit argument words and names one 64-bit result. A `runtime fn` whose
parameters or result are flat records or enums (`docs/native/runtime-fn-setups-design.md`
§7.2, §7.3) encodes them as several ports of mixed widths, so a call to it
cannot be a `Call` region today, and the default setup's lowering would have
to inline it.

## Scope

- `Call` with several arguments and results at their widths, its evaluation
  and `lower_program`'s case, proved once.
- `program_eval_sources` at the new shape.

## Done when

A runtime fn taking and returning a `WcState`-shaped record is called from
two sites and its code is emitted once.

## Log

- 2026-11-05: gardener: cites a file it shares with [[function-ir-verified-lowering]] (`lib/native/function_ir/function_ir.hthr`).
- 2026-11-19: a program's last function returns two words (`Function.also`,
  RAX:RDX, docs/native/runtime-fn-setups-design.md §16.16), so a `runtime fn`
  returning a record of two 64-bit words compiles as a program's entry. A
  call still reads one word: calling such a function is what this issue
  leaves.
- 2026-11-21: built (docs/native/runtime-fn-setups-design.md §16.17). `Call`
  names its result words past the first (`also`), answers are word lists
  through the evaluator, stages and lowering (RDX, RCX, RSI, … inside a
  program), and an rt call passes an enum's words and reads back a record
  or an enum of word slots, or a `Bool`. A narrow word or `Bool` passed
  to a call (a `Resize` before it) is left, as the §16.17 list says.
