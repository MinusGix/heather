---
title: A FunctionIR optimisation pass in Heather, proved once, inside Source::compile
status: closed
labels: [native,compiler,optimisation]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-31
updated: 2026-10-31
---

Round R10 of `docs/native/compiler-milestones-proposal.md` (§5, §7), milestone `hih-passes`: the first optimisation
pass that is a Heather function with its proof.

## Scope

- Constant folding and dead-node removal over FunctionIR regions, proved once to preserve `eval`, and run inside `Source::compile`.
- No per-program proof. The pass's theorem composes with `native_compile_correct`.

## Done when

The regression tools (`hih-tools`' nine) build with smaller code and unchanged GNU results.

## Log

**2026-10-31: landed.** The pass is `List::optimised(nodes, out)` in
`lib/native/function_ir/function_ir_pass.hthr`: a fold of each node whose
result is one number at every width (`Const`, `Move` of a known word, a
comparison's bit, `BitAnd`/`BitOr`/`BitXor` of bits), then removal of every
node whose word nothing later reads and the leaf's live set does not need.
Its theorem `List::optimised_runs` says the optimised leaf leaves the same
buffers and the same number in every live word, at every width; that is the
only proof, no per-program one.

Why this pass: over the ten tools' certificates, dead nodes were the payoff
(every tool had some, nearly all `Const`s whose word no later statement
reads) and folds within one leaf were rare (truth chains such as
`num(1).truth()`); folding is kept because it turns those chains into a
dead-node shape. Why it runs inside leaf emission (`Prog::computes_best` in
`native_compile.hthr`) rather than as a source-to-source pass before
`Source::compile`: the compile already knows each leaf's live-after set and
already claims only live words agree (`Target::Held`), so the pass's theorem
plugs into `Stmt::emit_runs` locally (`Target::goes_computes_best`,
`native_compile_pass.hthr`). The emission checks the optimised leaf against
the same apartness and live-in conditions as the original and falls back to
the original leaf when they fail, so the proof needs no new invariant. Byte
nodes are never touched, so label names and the Rust allocator are
unchanged.

Every tool builds smaller with its certificate kernel-checked (a few to a
few dozen bytes each; the largest drops are in the tools with the most
leaves). GNU results are the native tools suite's.

`Source::refusal` still reads the source before the pass, so a leaf refused
only for a node the pass drops as dead now compiles; the
`narrow_mixed_leaf` probe exits with its narrow word so it stays refused.

Left: arithmetic folds at an open width and constants across leaves,
[[function-ir-pass-arithmetic-folds]].
