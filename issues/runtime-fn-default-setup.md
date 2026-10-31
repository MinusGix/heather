---
title: The runtime fn generator in Heather and the default setup's pure fragment
status: open
labels: [native,compiler,metaprogramming]
area: heather-in-heather
milestone: [nh-front]
created: 2026-10-31
updated: 2026-10-31
---

Round R5 of `docs/compiler-milestones-proposal.md` (§4.2 N1, §7): the `runtime fn` generator and the default
setup's pure fragment.

## Scope

- The generator, written in Heather, as [[runtime-fn-setups-design]] decides it.
- The default setup's pure fragment and its lowering into `Source` leaves and FunctionIR regions, with an agreement certificate in `compile-x86`'s `_agrees` form.
- `compile-x86`'s Rust reflector (`crates/elab/src/function_ir_source/`) is retired onto the Heather generator.

## Done when

A `wc` step over a `WcState` record and the decimal formatter, marked `runtime fn`, compile into a tool that passes its GNU test, and `compile-x86`'s examples pass through the Heather generator.

## What it assumes from elsewhere

- **[[pure-imperative-statements]]** owns the imperative spellings. Until it lands, the fragment's examples are written with `match` and recursion.
