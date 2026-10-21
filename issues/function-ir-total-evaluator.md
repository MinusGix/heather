---
title: A total evaluator for FunctionIR, agreeing with its equations
status: open
labels: [native,ir,proofs]
area: heather-in-heather
milestone: [hih-pl-source]
created: 2026-10-21
updated: 2026-10-21
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
