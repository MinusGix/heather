---
title: Loops in the verified lowering, before B2 burns the only loop compilation
status: closed
labels: [native,x86,ir,proofs]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-21
updated: 2026-10-22
---

FunctionIR has loops (`lib/function_ir_loop.hthr`,
`docs/function-ir-readonly-loops.md`), and the per-function certificate
path compiles them (`function_ir_loop_x86`, `function_ir_loop_trace`,
`crates/elab/src/function_ir_source/loop_native.rs` and `readonly_loop.rs`).
None of [[function-ir-verified-lowering]]'s four rounds lowers a loop:
they cover straight-line regions, conditionals, calls and the stack, and
the CLI. Burn B2 (`docs/native-program-logic-design.md` §3.2) deletes the
old loop path, so as planned it would leave no way to compile a loop until
the effectful source exists.

Found while mapping the native state for Minus (2026-10-21); he asked for
gaps like this to be filed.

## The decision this waits on

Where loops live is a sub-question of the effectful source's shape
([[native-effect-source-compiler]], design §10). There are two options:

1. **One loop construct, in the effectful layer.** A pure loop is a layer
   loop that makes no calls, and [[native-loop-rule]]'s `loop_at` proves
   both kinds, with the variant doing the work for pure loops. FunctionIR
   regions stay loop-free, which is what S4 already lowers, so this issue
   then reduces to "no S4 round needed". The price is that a pure function
   with a loop denotes a tree over `Events::none()`, read back through
   `ITree::thread` as an `Option`. That is honest about non-termination,
   but every caller sees the `Option`.
2. **FunctionIR keeps its loops.** S4 gains a fifth round that lowers them,
   proved with a pure instance of the same loop rule (the register-file
   form of `Site::Runs` from round 2, iterated under a variant).

## Scope

- Decide 1 or 2, together with S3's source decision.
- For 2: a lowering round over `function_ir_loop`'s loop regions, with
  its theorem stated over every placement like rounds 1–3. `loop.hthr`-style
  examples go through it before B2 starts.
- Either way, B2 does not delete the old loop path until loops compile
  through the new route.

## What it assumes from elsewhere

- **[[function-ir-verified-lowering]]** owns the lowering and its rounds.
- **[[native-loop-rule]]** owns `loop_at`.
- **[[native-effect-source-compiler]]** owns the source's shape.

## Log

- 2026-10-21: `docs/native-effect-source-design.md` §5 adds a third option and recommends it, pending Minus's decision: **split loops by totality**. FunctionIR gains a *bounded* loop (at most `bound` passes, with an early-exit bit; `bounded_readonly`'s shape), which keeps FunctionIR total and is lowered by a fifth S4 round proved by induction on the bound; the effectful layer keeps the one *general* loop, proved by `loop_at` with the tree's remaining fuel as the ghost variant. Option 1 would give total pure functions a partial meaning; option 2 would make FunctionIR's evaluator need fuel.
- 2026-10-22: DECIDED (Minus): the totality split. FunctionIR gains a bounded loop with an explicit `Exhausted` outcome (a `Wf`-defined function takes its measure as bound), lowered by S4 round 5, which B2 waits for; general loops are the effectful layer's.
- 2026-10-22: Done as S4 round 5 ([[function-ir-verified-lowering]], "Round 5 as built"): `StructuredRegion::Loop` with `LoopRuns`, lowered in `emit_calls` and proved in `lower_program_correct`. `loop_runs_unexhausted` is the Wf route; its bound is the measure plus one, or the measure where it stays positive. B2 can now move the old loop path's examples onto it.
