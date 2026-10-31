---
title: Inline reflected Heather word functions as builder helpers
status: open
labels: [native,frontend,ergonomics]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-27
updated: 2026-10-31
---

Round 5 of `docs/native-real-programs-plan.md` (§3.3) asked for pure helpers
written as ordinary Heather word functions, inlined into a tool as their
reflected FunctionIR regions (the `compile-x86` reflector,
`crates/elab/src/function_ir_source.rs`) with the reflector's certificate
that the region evaluates to the function. [[native-source-builder]] landed
without it.

Today a helper is a Heather function over the builder's values
(`fn is_lower(c: Val) → Val`), inlined where it is called. That covers
straight-line helpers, but its meaning is only the nodes it lowers to: a
spec proof about a tool cannot cite the helper as a function on words. A
reflected helper would carry that meaning, and helpers with conditionals or
loops (decimal formatting, [[native-decimal-io]]) need it most.

## Scope

- A `Val` (or `Act`) form naming a reflected word function and its
  arguments; the builder places the region's inputs and outputs in words.
- The region's agreement certificate stated beside the tool, so a spec
  proof reads the helper's result as the function's value.

## What it assumes from elsewhere

- **[[native-compile-wider-leaves]]** owns compiling the `Conditional` and
  `Loop` regions a reflected helper with branches or loops lowers to; until
  it lands only dataflow helpers would compile.

## Log

- 2026-10-31: 2026-10-31: hih-tools closed (docs/compiler-milestones-proposal.md §8). Moved to nh-front: [[runtime-fn-setups-design]] folds this in or closes it.
- 2026-10-31: 2026-10-31: `docs/runtime-fn-setups-design.md` §10: kept as the near-term stepping stone (through the Rust reflector). Its builder-facing form survives R5: in [[runtime-fn-default-setup]] the helper form takes a function with a `Compile` instance (from a `runtime fn` or by hand) instead of a function the Rust reflector reads.
