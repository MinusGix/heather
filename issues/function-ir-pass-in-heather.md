---
title: A FunctionIR optimisation pass in Heather, proved once, inside Source::compile
status: open
labels: [native,compiler,optimisation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-31
updated: 2026-10-31
---

Round R10 of `docs/compiler-milestones-proposal.md` (§5, §7), milestone `hih-passes`: the first optimisation
pass that is a Heather function with its proof.

## Scope

- Constant folding and dead-node removal over FunctionIR regions, proved once to preserve `eval`, and run inside `Source::compile`.
- No per-program proof. The pass's theorem composes with `native_compile_correct`.

## Done when

The regression tools (`hih-tools`' nine) build with smaller code and unchanged GNU results.
