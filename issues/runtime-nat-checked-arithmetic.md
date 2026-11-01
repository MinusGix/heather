---
title: Nat at run time: checked word arithmetic with overflow as a trap exit
status: open
labels: [native,compiler,datarepr]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-10-31
updated: 2026-10-31
---

`docs/runtime-fn-setups-design.md` §7.2 (decision 6): under the default
setup's first fragment, `Nat` is accepted only where a bound is structural
(a literal, a `Bytes` length or index, a loop count). General `Nat`
arithmetic at run time needs the narrowing of `docs/datarepr-design.md`
§2.4: a word with a checked operation, and overflow as a defined trap exit.

## Scope

- `Nat` in `rt::Ty` as a 64-bit word whose meaning is the `Nat` it encodes,
  with `+`, `*`, `-` (truncated) checked.
- Overflow as a defined exit of the program, so the agreement is partial
  correctness: if the program returns, its result is the function's.
- Needs an exit, which arrives with N3's `Source` statements.

## Done when

A runtime fn over `Nat` compiles, agrees with its function where it returns,
and a test drives it to the trap exit.
