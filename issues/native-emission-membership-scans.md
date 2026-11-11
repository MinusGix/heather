---
title: A leaf's emission is mostly membership scans over lists of word ids
status: open
labels: [performance,native,compiler]
area: heather-in-heather
created: 2026-11-11
updated: 2026-11-11
---

Found by [[native-tool-compile-attribution]], after its reads stopped repeating one another.

What is left of a native tool's `write-elf` is the compiler's own evaluation: each leaf is emitted once by the fork's read (`{p}_read_#_part`) and once by the kernel (`{p}_e_#`), and both run the library's `Stmt::emits` in the evaluator. A profile of the reads by the definition being unfolded says where that goes.

## Measured

2026-11-11, four-core cloud box, `sort_tool` cold, dev-profile binary at width one. The reads of the parts are 18.0 M evaluator steps (17.5 M of them the 127 whole parts' emissions, about 60 thousand a leaf). Charging each step to the definition most recently unfolded (a flat attribution: a caller's work after a call returns is charged to the callee):

| definition | steps | unfoldings |
|---|---|---|
| the global at position 75, by its place and count `Bool`'s generated eliminator (every `match` on a verdict) | 4.48 M | 633 k |
| `Nat::same` | 3.13 M | 260 k |
| the global at position 33, by its place and count `Or`'s generated eliminator (the `match` on `eq_dec`'s answer) | 1.22 M | 244 k |
| `function_ir_eval::absent` | 1.21 M | 158 k |
| `List::nth` | 0.82 M | 16 k |
| `Bool::and` | 0.77 M | 257 k |
| `Nat::eq_dec` | 0.72 M | 240 k |
| `Nat::differs` | 0.70 M | 234 k |
| everything else (1,255 definitions) | 4.95 M | |

So about two thirds of the compile's evaluation is one chain: `absent(id, ids)` scanning a list of word ids, each element through `Nat::differs`, which asks `Nat::eq_dec` for a proof-carrying answer (`Inl`/`Inr`), which asks `Nat::same`, and the verdict is matched three times on the way back (in `eq_dec`, in `differs` and in `&&`). That is about fifty evaluator steps for each element scanned, and a leaf scans about a thousand elements (liveness, apartness and the pass's `needs` are all list sets of ids).

The kernel's side has the same shape: its 127 whole-part statements are 14.8 M steps.

## Directions

- The constant: `Nat::differs` and `Nat::matches` as `Nat::same` and its negation, with `differs_ne` and its siblings proved from `same_sound`/`ne_of_same`, so a comparison builds no `Or`. `absent` could match on `same` directly. This is a change at the root of `lib/native/function_ir`, so every native module re-elaborates, and proofs that unfold `differs` through `eq_dec` need their step restated.
- The exponent: the sets as something a membership test does not scan. Word ids are small and dense, so a set as a `BitVec` (the kernel has native bitvector values) makes `absent` one `testBit` and union, difference and `within` one word operation each. That is a representation change across `native_alloc` and `native_compile` and their proofs, worth a design note first.
- Either way the measure is `scripts/bench-probes --heavy --filter native/elf-cold` (`eval_steps` on `sort_tool` and `tac_tool`), and the reads' and the `e_#` rows' steps per leaf.

## Done when

A leaf's emission costs visibly fewer steps on `sort_tool` and `tac_tool` cold, in the read and in the kernel's statement both, with the ELF bytes unchanged.
