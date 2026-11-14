---
title: A proved pass recognising rotates written as two shifts
status: open
labels: [native,compiler,function-ir,x86]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-10
updated: 2026-11-14
---

A rotate written as two shifts and an OR compiles to five instructions
(`MOV SHR MOV SHL OR`; SHA-512's Σ0 in `native-roadmap/bsig0_64.s`). One
`ROR` does it. Recognising the idiom is a rewrite with a side condition
(`a + b = w`), which is the smallest honest instance of "untrusted search
over checked witnesses" after constant folding.

## Scope

- A FunctionIR `Rotate` node, valued by `BitVec::rotr`
  ([[bitvec-rotates-and-wide-ops]]), and its lowering to `ROR` by an
  immediate ([[x86-narrow-and-rotate-forms]]).
- The rewrite `(x >> a) | (x << b) → rotr(x, a)` when `a + b = w`, as a
  local law of the certified pass algebra
  (`docs/certified-pass-algebra-probe.md`), composed as one more diagram
  (`function_ir_pass_diagrams.hthr`).
- Worth weighing: the e-graph library (`lib/std/data/egraph.hthr`) as the
  search, so later peepholes are rules and not passes.

## Done when

SHA-512's Σ0 certifies with one rotate instruction per rotate, and the pass
is proved once.

## What it assumes from elsewhere

- **[[function-ir-pass-arithmetic-folds]]** owns the fold pass this sits
  beside.

## Log

- 2026-11-14: The node and its lowering exist: `RotateRight(width, output, value, amount)` in `function_ir.hthr`, meaning `values(width, value).rotr(amount)`, lowered at width 32 and counts below 32 to `ROR r32, imm8` (`File::rotate_right`). The theorem a rewrite cites is `rotate_right_of_shifts`: `LogicalShiftRight(w, r, x, k)`, `ShiftLeft(w, l, x, w - k)` and `BitOr(w, o, r, l)` give `RotateRight(w, o, x, k)`'s equation (it is `rotr`'s definition unfolded). `lib/_tests/native/function_ir/function_ir_rotate_tests.hthr` states the optimizer clause for it and proves it sound in one line (`rotate_of_shifts_sound`); adding that clause to `rules()` is the optimizer's (`function_ir_rules.hthr`). Until then no compiled program contains a rotate: `runtime fn`s reflect `rotr` as its shift pair.
