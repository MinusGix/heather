---
title: A runtime fn over a Bytes(n) that calls a loop taking facts is refused
status: open
labels: [native,runtime-fn,proofs]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-18
updated: 2026-11-18
---

A loop over a `Bytes(n)` that takes facts now gets its theorem
(`docs/native/span-record-design.md`, "Loops that take facts"): a
recursive `runtime fn` with `inside: ∥stop <= s.len()∥` is compiled and
`f::runs_bytes` states agreement at the fact
(`lib/_tests/native/runtime/runtime_bytes_tests.hthr`, `zero_from`).

Its **caller** is refused. The probe is `zero_upto` in the same file: a
`while … invariant stop <= s.len()` lifts to `zero_upto_loop`, which takes
the invariant as a fact, and

> `Bytes::zero_upto` cannot be a runtime fn of a `Bytes(n)`: it calls
> `Bytes::zero_upto_loop`, which takes facts: a caller's theorem would need
> them at the call, which is not built yet

The sort (`examples/sort`) is this shape: its outer loop calls its inner
loop, which takes `∥j <= i∥` and `∥i < s.len()∥`.

## Why the straight theorem cannot take it as it stands

A caller's theorem (`runtime_bytes_straight`, `FTm::over_spec`) is its
reflection's meaning over a world (`BWorld`) **by conversion**, and the
world holds each callee's agreement with its code at **every** record
(`BWorld::agrees_each`). A fact-taking callee agrees only where its facts
hold. Its meaning in the world would be its guarded run
(`FFun::when(ok, …)`), and the caller's own spec calls `c(args, q)`, which
is the guarded run only through `FFun::when_true` at `q`: the test is
stuck on the caller's words, so conversion cannot see it. Rewriting the
call is not available in general either: there is no funext, and a call
sits under the continuations of the statements before it.

## Two routes

1. **Agreement where the facts hold, discharged at each call.** The world
   holds a fact-taking callee's agreement only at passing states, and the
   meaning's call node carries the obligation `ok(args) = True`. The caller
   discharges it from the fact term its own call passes (`FFun::bit_of`
   of `q`), which the generator reads off the spec at each call. General
   (any call position the reflection walks), and the straight theorem's
   walk has to carry the obligations.
2. **A caller's companion extensional in its callee.** As `f#ext` makes a
   measured body extensional in its own recursion at the measure, an
   elaborator companion makes a caller's body extensional in a named
   callee where that callee's facts hold. The world's entry is then the
   callee's code read over records, whose agreement is trivial, and
   `c::runs_bytes` is the extensionality's hypothesis. Elaborator work,
   and it refuses calls under a `λ` as `f#ext` does.

## Done when

`zero_upto`'s `expect-error` comes off: the caller of a fact-taking loop
gets `runs_bytes` with nothing proved by hand, and the sort's two loops
follow.
