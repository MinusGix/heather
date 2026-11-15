---
title: A proved pass recognising rotates written as two shifts
status: open
labels: [native,compiler,function-ir,x86]
area: heather-in-heather
milestone: [hih-passes]
created: 2026-11-10
updated: 2026-11-10
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
  (`docs/metaprogramming/certified-pass-algebra-probe.md`), composed as one more diagram
  (`function_ir_pass_diagrams.hthr`).
- Worth weighing: the e-graph library (`lib/std/data/egraph.hthr`) as the
  search, so later peepholes are rules and not passes.

## Done when

SHA-512's Σ0 certifies with one rotate instruction per rotate, and the pass
is proved once.

## What it assumes from elsewhere

- **[[function-ir-pass-arithmetic-folds]]** owns the fold pass this sits
  beside.
