---
title: port_fib's loop is refused by the register planner (it carried the whole context until 3c)
status: open
thread: Rebuild loops on one combinator
labels: [native,runtime-fn]
area: heather-in-heather
created: 2026-11-20
updated: 2026-11-21
---

A `runtime fn` loop (`Tm::Iterate`, docs/language/loop-combinator-design.md
§6.2) lowers to a FunctionIR loop region whose passes see only the region's
parameters, so `Tm::lower_iterate` carries every word of the context
(`Tm::carry` over all of `g`), read by the loop or not. `port_fib`
(`lib/_tests/native/runtime/runtime_ports_tests.hthr`) carries ten words
plus its three state words, and `compile-x86`'s planner refuses it ("a
next state word is in no register"); it checks and runs by `refl`, it does
not reach x86.

## Fix

Carry only the variables the test and body read, and give the dropped ones
a port the pass never reads. The soundness proof then needs:

- a lemma that a term's meaning does not depend on a variable it does not
  read (`Tm::sem` at two environments that agree on the read variables is
  equal), with the extensionality steps for `Loop::steps` and `Pick`'s
  choice;
- a value for a dropped variable of a word or record type in the
  environment the pass is lowered against.

Alternatively the elaborator could write fewer context variables at the
loop (constants inlined), but that only moves the limit.

## Log

- 2026-11-21: Fixed: a loop carries the variables its test and body read (`Tm::vars`,
  checked by `Tm::check_within`), and leaves out the rest when a pass can read a
  value of their code back (`Ty::drop_at`: a word, a count or a buffer from any
  port, a record of the state's code from the state's own ports).
  `Tm::sem_kept` proves a term's meaning is the same at two environments that
  agree on what it reads (with `Loop::steps_ext` and `EnumInfo::choose_ext`),
  and the pass runs at `Env::refill`. `port_fib`'s loop now carries its three
  state words and `n` (was ten words). It still does not reach x86: the
  register planner refuses the pass ("a next state word (20, 21, 22, 11) is in
  no register"), the same for a `while` that swaps (`let t = a + b; a := b;
  b := t`) while one that only adds compiles. Left open for that, which is the
  planner's (`StructuredRegion::plan_in`, the branch's meet).
