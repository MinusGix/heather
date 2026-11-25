---
title: FunctionIR ids typed word or reference: the lowered valuation, and the per-node check that replaces placeless
status: open
labels: [ownership,native,design]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

The reference-cells experiment ([[ownership-reference-cells-spike]]) found that FunctionIR's register invariant need not split by kind: a reference is a word in the valuation lowered through the injection (`lowered_values`), and `Held::Rep` at kind `Word` over that valuation is the toy's register invariant (`registers_represent`, `lib/native/reference_cells/reference_cells_bridges.hthr`). `File`, `Kind`, `Held::Rep` and the theorems stated over `File::Represents` keep their statements.

What carries the kind instead is the valuation, and for FunctionIR that needs two things the toy got from its kind-dispatching meaning:

1. **Ids typed by kind.** FunctionIR's `Valuation()` is bit vectors by id. References need a second map (`refs: Nat → Option<Loc>`, or a `Value` valuation) and a lowered valuation that overrides reference ids with their addresses.
2. **A per-node check that word nodes read no reference id.** A word node's equation over the meaning's valuation transfers to the lowered one only if it reads no reference: an `ADD` of a reference's id would compute on an address the meaning never names. This check is what `placeless` (`function_ir_placeless`) becomes: local to a node, no taint fixpoint through loops, and its meaning-level statement is the renaming theorem (`run_renames`, `reference_cells.hthr`).

New nodes beside the old: a reference load and store (the same `MOV`s as a word's) and a byte load through a reference, each with an emit theorem in the style of `load_emits` over the injection.

## Done when

FunctionIR has reference ids and the three nodes, a region using them lowers with its theorem through the existing `File` machinery at the lowered valuation, and `placeless` is retired for regions whose addresses are references (or kept for buffer homes, with the reason written).

## What it assumes from elsewhere

- **[[ownership-reference-cells-spike]]** owns `lowered_values` and `held_word_rep`. Assumed here: only that `Held::Rep` at kind `Word` over the lowered valuation is the register invariant a reference needs.
