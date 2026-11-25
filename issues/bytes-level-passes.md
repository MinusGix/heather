---
title: The optimizer's passes over the bytes level, each proved Refines
status: open
labels: [native,function-ir,optimizer,memory,ownership]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

Stage 2 of `docs/language/ownership-design.md` §17.5: the optimizer's passes over the bytes level (`lib/native/bytes_level/`), each proved as one statement, `Refines(p, pass(p))`: every answer of the input is an answer of the output ([[bytes-level-language]]). There is no second meaning, no definedness side condition and no bridge between forms.

## Scope

- **Word rules lift unchanged.** A rule of `function_ir_rule` rewrites `Compute` nodes. Its existing soundness (the node's equations) gives `Refines` through one lemma: a leaf whose word steps agree answers alike.
- **Memory passes** need the equivalence `Refines` compares heaps by (`Memory::Same`: the same bytes, the same entries, the same blocks writable) to be a congruence for `take` and `put`. That needs the shadow's entries apart from each other (no two overlap). Canonical memories have them apart by construction, but it is not yet stated (`Memory::Canonical` says only that a reference's bytes are zero), so it is stated and kept first. Then: store-to-load forwarding, a dead store, a load of a reference followed through, each a `Refines` theorem with its probe and control.
- **Placeless passes.** A pass that is a function of the program alone keeps `run_renames` for free, since it holds of every program. Nothing per pass.
- What the optimizer does today over FunctionIR (`function_ir_optimize`, `function_ir_pass`) is the list to cover. A pass that exists only because of buffers by number (views, lends, `placeless`) has nothing to carry over.

## Done when

The optimizer's word passes and at least forwarding and dead-store elimination run over the bytes level, each proved `Refines`, each with a probe and a control, and the list of the old passes not carried over is in the log with the reason for each.

## What it assumes from elsewhere

- **[[bytes-level-language]]** owns `Refines`, `Memory::Same` and the canonical heap.
