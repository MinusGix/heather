---
title: Reflect and plan bounded loops for the verified compile path
status: closed
labels: [native,ir]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-10-23
updated: 2026-10-25
---

[[function-ir-verified-lowering]] round 5 lowers and proves FunctionIR's
bounded `Loop`, with placements written by hand. Round 4's `compile-x86`
path has no route to it: the reflector
(`crates/elab/src/function_ir_source/program.rs`) refuses recursion, and
`StructuredRegion::plan_from`'s `Loop` arm places nothing. Two pieces are
missing:

- **The reflector.** Structural recursion, or a `fuel`/measure-bounded
  helper, becomes a `Loop` with `bound` taken from the measure
  (`loop_runs_unexhausted`'s reading: the measure at entry plus one in
  general). The certificate's `refl` agreement then needs the evaluator's
  loop to unfold against the source's recursion, which is untested at open
  arguments.
- **The planner.** It must pick the state, counter and flag registers,
  pairwise apart and caller-saved, as `LoopRegisters::Apart` requires.
  The loop is a barrier, so the planner's file after it is the outputs and
  the exhausted bit only.

The old per-function loop path (`function_ir_loop`) is what B2 replaces
with this.

## Log

**2026-10-25: done for a fuelled recursion in the exported function's
tail.** `compile-x86` compiles `h(fuel: Nat, x…: BitVec(64)) → BitVec(64)`,
matching its fuel `Zero`/`Succ(k)` and called as the root's result
`h(w.toNat(), e…)` with one to four words, to a `Loop` whose bound is `w`
(`examples/x86-native/loop_*.hthr`; `native_program.rs`'s
`programs_with_loops_execute` runs them against C).

- **Reflection** (`crates/elab/src/function_ir_source/program.rs`,
  `ends_in_loop`). The `Succ`
  arm becomes the pass: a decision tree whose leaves either recurse
  (`after(k, …)`, next state and tag word 0) or return (result in state
  word 0, tag 1); `exit` is `tag = 1`. Words the recursion passes on
  unchanged stay outer variables, so the elaborator's `ElimNat` over the
  varying words only is matched as it is. The `Zero` arm is the `post`'s
  exhausted branch. A step that reads `k` or the recursion as a value is
  refused, and so is a loop anywhere but the root's tail
  ([[function-ir-loops-anywhere]]); `Wf` recursion on a measure is
  [[function-ir-loop-measure-recursion]].
- **Planning** (`function_ir_lower_structured`'s `Loop` arm). State words
  stay in the registers their inputs already hold where they are free; the
  counter and flag take free registers apart from them; the pass is planned
  in the file of state, counter and flag; after the loop the file is the
  exhausted bit and the outputs.
- **Proof.** `function_ir_compile::loop_eval_agrees` is the generic `Nat`
  induction: if every pass agrees with one unfolding of the source's step,
  the loop agrees with the source's recursion at any fuel.
  The certificate states one pass's obligation with the tree's comparisons
  abstracted as `Bool`s and splits them by explicit convoys (`_pass_cased`):
  `split_all` builds a term the kernel rejects there
  ([[split-all-nested-scrutinee-kernel-reject]]). The root is then met by a
  chain of generic lemma instances (`program_eval_last`,
  `function_eval_body`, `compose_eval`, `loop_then_eval`) whose stated types
  are syntactic, never by a conversion: at a literal fuel that conversion
  runs every pass.

Code size: the pass spends a tag word, a 64-bit immediate per tag and a
move per state word at a returning leaf. A pass whose leaves all recurse
but one, or a tag folded into the exit comparison, would shed them; nothing
waits on it.
