---
title: Effectful callees in rt, lowered to Source procedure calls
status: open
labels: [native,effects,runtime]
area: heather-in-heather
milestone: [nh-effects]
created: 2026-11-08
updated: 2026-11-08
---

`ETm` has no call of another effectful function
(`docs/effects-capabilities-design.md` §8.4: "an effectful callee (`EFun`
calling `EFun`) is not modelled"), so effectful code compiles only as one
function and a helper over `Io` has to be inlined by hand. That is the
coarsest non-locality in the pipeline (`docs/effects-locality-design.md`
§3 N6, §5.4 item 1).

## Scope

- An `ETm` node calling an effectful function on variables, binding its
  answer and continuing with the world after it; its meaning is the
  callee's `ETm::sem` (or its `Partial` meaning when it loops).
- Lowered to a `Source` procedure call (`docs/native-procedures-design.md`):
  a callee starts with only its parameters and returns only results and
  buffers, so the call's buffers are the callee's in/out set.
- Its case of `ETm::lower_sound`/`lower_reads` by `Io::reads_bind` and the
  procedure contract, proved once.
- The reflector reads a call of another `mut self` method over `Io` that is
  itself reflectable as this node, so `Io::write_all` can be a callee of
  `cat`.

## What it assumes from elsewhere

- **[[effects-uniqueness-surface]]** owns the reflector and `ETm`.
- **[[native-procedure-contracts]]** owns the procedure contract.
