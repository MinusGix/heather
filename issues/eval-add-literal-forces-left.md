---
title: The evaluator forces e in e + 1 where Succ(e) stays lazy
status: open
labels: [kernel,perf,eval]
area: kernel
created: 2026-11-17
updated: 2026-11-17
---

`Succ(e)` evaluates to a successor of a thunk; `e + 1` folds through the
number algebra ([[succ-chain-numbers-fold-unary]]) and forces `e` first.
The two are convertible (`Nat::add` recurses on its second argument), but a
definition evaluated over long data behaves differently: respelling
`List::len`'s step `Succ(t.len())` as `t.len() + 1` made
`lexer_records.hthr`'s check overflow the evaluator's stack, and
`native_compile_correct` hit the library gate's CPU rail.

So the `n + 1` respelling (Minus, 2026-11-17; [[unify-plus-one-pattern]])
rewrote theorems whole but `fn`s only up to their bodies. Function bodies
keep `Succ` until `e + k` at a literal `k` evaluates as `k` lazy successors
of `e` (or the fold stops forcing a left operand it only wraps).
