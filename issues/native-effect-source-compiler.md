---
title: An effectful source denoting Linux trees, and its compiler proved correct once
status: closed
labels: [native,x86,ir,proofs,design]
area: heather-in-heather
blocked-by: [native-loop-rule, function-ir-verified-lowering]
created: 2026-10-21
updated: 2026-10-25
milestone: [hih-pl-source]
---

Round S3 of `docs/native-program-logic-design.md` (§7): an effectful source
whose programs denote Linux trees, its compiler to `Prog` written in
Heather, and the compiler's correctness theorem proved once.

## Scope

- Decide the source: FunctionIR grown with effect nodes, or a small
  tree-shaped layer whose leaves are FunctionIR regions (the design's lean).
- `denote` (compositional: sequencing is `bind`, loops are `iter`) and
  `compile`, with the register and frame conventions stated once as the
  invariant between constructs.
- One lemma per construct, over abstract inputs, proved with `Wp` and
  `loop_at`; the theorem by induction on the source: `Sim` at `denote(p)` of
  the assembled `compile(p)`.
- Whether the read's buffer size is fixed by the source or abstracted
  (design §10, question 1).

## What it assumes from elsewhere

- **[[native-one-wp]]**, **[[native-loop-rule]]** own the target-side tools.
- **[[function-ir-verified-lowering]]** owns pure regions' code; assumed
  here only as `Proved` items with the lowering's theorem as contract.
- **[[effects-direction]]** owns the surface that elaborates to this source.

## Log

- 2026-10-21: Minus's answers (design §10): the surface is uniqueness threading that denotes trees (item 5); the source's shape stays open, with the input for this round in item 6 (external effects in the tree layer, internal effects as FunctionIR state edges; decide by writing `tr` both ways first). Where loops live is decided with it: [[function-ir-lowering-loops]]. Before B2, also [[function-ir-source-denotation-after-b2]].
- 2026-10-21: Design for Minus's decision: `docs/native-effect-source-design.md`. Recommends a control layer (calls, sequencing, branching, the general loop, exit; `denote` one tree construct per constructor) over FunctionIR made the *total* level (dataflow, conditionals, total calls, a bounded loop, buffers on state edges), so S4's theorem enters unchanged as `Proved` contracts. Writing `tr` both ways showed FunctionIR with effect nodes would restate S4's three rounds. Gaps filed: [[function-ir-total-evaluator]], [[wp-proved-memory-contracts]], [[function-ir-buffer-state-edges]], [[itree-iter-simulation]]. Proposed rounds S3.0–S3.3 (§10 there), first program `cat`.
- 2026-10-22: DECIDED (Minus): option A (control layer over a total FunctionIR) and L3 (bounded loop with `Exhausted` in FunctionIR, the general loop in the layer). The principled case is design §11 (PR #123). Next: rounds S3.0 ([[function-ir-total-evaluator]]) and S3.1 (the layer, `denote`, `cat`).
- 2026-10-22: S3.0 landed as PR #127: `lib/native/function_ir/function_ir_eval.hthr`, a total evaluator proved against the relational semantics ([[function-ir-total-evaluator]], closed).
- 2026-10-22: S3.1, the layer: `lib/native/native_source.hthr`. It has `Env` (word and buffer files, kept as data so each value is computed once), calls that clamp to their buffers, `Stmt`/`Flow`, `denote` (`Ret`/`Vis`/`bind`/`iter`), `Stmt::grows` and `Source::denote → Program`. `cat` is written in it and run against a scripted world by `refl` (`crates/elab/tests/fixtures/native_source_cat.hthr`). Longer runs hit the kernel's bounded value cache ([[kernel-value-cache-evaluation-thrash]]). cat's `Implements` against `tr_spec` is [[native-source-cat-implements]]. Next: S3.2 (compile the layer and its theorem).
- 2026-10-22: 2026-10-22: Runs by refl no longer meet a bounded value cache: the kernel keeps what a query forced, and cat copying three bytes one at a time checks ([[kernel-value-cache-evaluation-thrash]]).
- 2026-10-23: 2026-10-23: S3.1's done-when holds: cat's source implements `tr_spec(λ b => b)` at every capacity `0 < c < 2^63` ([[native-source-cat-implements]], closed; `lib/native/native_cat_spec.hthr`). Source proofs go statement by statement through `lib/native/native_source_sim.hthr` (simulation up to a continuation, docs/itree-simulation-design.md §6). cat now lives in `lib/native/native_cat.hthr`.
- 2026-10-25: S3.2 landed: the compiler (`lib/native/native_compile.hthr`) and its theorem, `native_compile_correct` (`lib/native/native_compile_correct.hthr`): a program `Source::compile` builds, run from its first byte with its code resident and its data region zero, simulates `src.denote()` at every fuel. The shape differs from design §7.4–7.5 in three ways. The environment lives wholly in one data region (words in slots, buffers after them, a scratch range for reads), so the invariant between statements is memory alone (`Target::Placed`, `native_compile_region.hthr`) and no placement is threaded. The construct lemmas are proved directly over the code's `Goes` claim, one rule per instruction form (`native_compile_steps`/`segments`), not through `Wp`. And a `Compute` leaf is a register-only dataflow region lowered by S4 (`Region::lower_correct`), so no `Proved` contract with memory was needed ([[wp-proved-memory-contracts]] stays for leaves that spill or call). The statement induction is `Stmt::emit_runs` (a continuation-form claim, `Target::Runs`; `Repeat` by induction on the loop's fuel). cat compiled at the I/O image's page and loaded past a 232-byte header sends to stdout what it read (`cat_native_sends`, `lib/native/native_cat_compiled.hthr`), with only the compile and its length evaluated. Refused for now, each filed: other region shapes as leaves ([[native-compile-wider-leaves]]), open/close/stat ([[native-compile-other-calls]]), and the code's shape ([[native-compiled-code-shape]]).
