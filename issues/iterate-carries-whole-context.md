---
title: A runtime loop carries the whole context, so port_fib misses registers
status: open
thread: Rebuild loops on one combinator
labels: [native,runtime-fn]
area: heather-in-heather
created: 2026-11-20
updated: 2026-11-20
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
