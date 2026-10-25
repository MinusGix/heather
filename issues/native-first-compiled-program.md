---
title: tr through the verified compiler, then burn the per-function certificates (B2)
status: open
labels: [native,x86,proofs]
area: heather-in-heather
created: 2026-10-21
updated: 2026-10-25
milestone: [hih-pl-first-program]
---

Round S5 of `docs/native-program-logic-design.md` (§9): the first program
built through the verified compiler.

## Scope

- `tr` written in the effectful source, built by `compile`, with its claim
  `Sim(io_linux(), denote(tr))` from the compiler's theorem and its stdout
  fact from its tree. No per-program proof beyond instantiating the theorem.
- Measure what checking costs now: evaluating `compile` in the kernel
  (design §10, question 3), against `native-v0`'s certificate cost.
- Then burn B2 (design §3.2): the per-function certificate path and the
  old execution shapes.

## What it assumes from elsewhere

- **[[native-effect-source-compiler]]** owns the source, `compile` and the
  theorem.
- **[[function-ir-verified-lowering]]** owns the pure lowering B2 replaces
  the old path with.

## Log

- 2026-10-24: B2 landed ahead of `tr` (2026-10-24, Minus's call): the per-function path is gone and the examples compile through the verified path. This issue keeps `tr`.
- 2026-10-25: cat, which is `tr` of the identity, now goes through the verified compiler: `cat_native_sends` (`lib/native/native_cat_compiled.hthr`) instantiates `native_compile_correct` at `cat(1024)` compiled by evaluation and loaded past a 232-byte header, and chains `cat_sends` (from `cat_implements`) onto the machine's runs. The only per-program proof is the tree-to-tree one cat already had. `tr` with a byte map other than the identity needs a leaf that maps a buffer, which waits on [[function-ir-buffer-state-edges]]. The cost question (evaluating `compile` in the kernel) has one data point: the compile, its laid-out check and its length each fit in one kernel query, but evaluating the compile twice in one query runs out of fuel, so a client names the result once (`Option::some_unwrap`) and reads the laid-out fact off the compile (`Source::compile_laid`). Running the bytes as a real executable is [[native-cat-executable]].
