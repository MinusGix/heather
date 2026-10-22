---
title: A total evaluator for FunctionIR, agreeing with its equations
status: closed
labels: [native,ir,proofs]
area: heather-in-heather
milestone: [hih-pl-source]
created: 2026-10-21
updated: 2026-10-22
---

FunctionIR's meaning is relational: `RegionHolds`,
`StructuredRegionHoldsIn` and `Function::Computes` (`lib/function_ir.hthr`)
say that some valuation satisfies a region's equations. A tree has to
*compute* its next command from the values in hand, so the effectful
source's `denote` needs a function: `StructuredRegion::eval(callees, region,
env) → env`, and for a program, its functions evaluated last first as
`program_callees` orders them. Found while writing
`docs/native-effect-source-design.md` (§2.1); it is needed whatever shape
the source takes.

## Scope

- `Region::eval`, `StructuredRegion::eval` (conditionals by the bit, `Call`
  by the callee's own `eval`), `Function::eval` and a program's evaluator,
  all total by structural recursion.
- `eval_holds`: the evaluated valuation satisfies the equations, so every S4
  statement applies to it; and, for `Function`, `Computes` at the evaluated
  result.
- The S4 examples evaluated by `refl`.

## What it assumes from elsewhere

- **[[native-effect-source-compiler]]** owns the source that calls it.
- **[[function-ir-lowering-loops]]**: if FunctionIR gains the bounded loop,
  its `eval` is structural recursion on the bound and stays total.

## Log

- 2026-10-22: Done (round S3.0), `lib/function_ir_eval.hthr`. A value is set at every width at once, and a node's value is its equation's right side read at the width asked for, so no width is ever compared or transported. `eval` is total; the theorem asks a Bool `evaluable` computed by evaluation (no node reads its own output; nothing later writes an id earlier code mentions; no arm writes its condition; a call names a function of its arity whose result is not an argument; a function's parameters are distinct and unwritten). `StructuredRegion::eval_holds_in`: any valuation agreeing with the evaluated one on what a region mentions satisfies it, its calls answered by results callees may return. `program_eval_computes`: what `program_eval` returns for a call of the right arity is in `program_callees`. Examples (the lowering rounds' `pair`, a conditional `select` at literal and open arguments, eight refusals) in `crates/elab/tests/fixtures/function_ir_eval_examples.hthr`, with two kernel-refusal controls.
