---
title: Respelling function bodies as e + 1 broke one evaluation (not List::len)
status: closed
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

## Log

- 2026-11-17: The diagnosis above was wrong. Respelling `List::len` alone
  leaves `lexer_records.hthr` checking. Bisecting the body respelling found
  one definition: `Nat::sub`'s `Zero => Succ(m2)` arm. Spelled `m2 + 1`,
  `runtime fn` code evaluating `BitVec::ofNat(Nat::pow(2, 32) - 1)` ran out
  of memory (a one-line probe reproduces it in seconds). `Nat::sub` keeps
  `Succ` there, beside `Nat::add`'s own definition, and every other function
  body in the library is respelled. Why the subtraction's arm matters to the
  fold classes (`eval/probe.rs`) is not chased down; the probe is the
  reproduction if it ever is.
