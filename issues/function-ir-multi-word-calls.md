---
title: FunctionIR calls with several argument and result words at their widths
status: open
labels: [native,function-ir,compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
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
