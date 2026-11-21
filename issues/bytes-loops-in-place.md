---
title: A loop over a Bytes(n) receiver is still lifted as a method, not written in place on FTm::Loop
status: open
thread: Rebuild loops on one combinator
labels: [native,runtime-fn]
area: heather-in-heather
created: 2026-11-21
updated: 2026-11-21
---

Round 3c writes a `runtime fn`'s `while` and counted `for` over its
`List<u8>` receiver in place, as `loop::Loop::steps` over
`Mutated<span, S>`, which the reflector reads as one `FTm::Loop`
(docs/language/loop-combinator-design.md §6.3). A `Bytes(n)` receiver is not
routed there yet (`Lift::span_receiver` in `crates/elab/src/loops.rs`).

What was tried (2026-11-21), on `runtime_bytes_tests`' `Bytes::clear`:

- Routing a `Bytes(n)` receiver (its type is `TyKind::OfExpr(Bytes(n))`)
  elaborates. The step's equation with the turn (`f::loop::same`) could not
  be proved by `split_all`: the body's found proof (`s[i] := 0` finds
  `i < s.len()` from the test's equation) keeps the test in place. The step
  is now `loop::Pass::of_turn` and the equation is `Pass::step_of_turn`,
  proved once, for every span loop.
- The reflector reads the loop. The function's write-out over its span
  (`SpanWriting::written` in `runtime.hthr`) had no `Loop` arm; one that
  writes `Loop::after(Loop::steps(passes, λ p => Loop::after(p, λ o v =>
  Step::turn(test, λ _ => body, p)), Mutated(span, init)), λ span x => rest)`
  is accepted, but `f::runs_over` then runs out of conversion fuel.

The likely cause: any mismatch between the written pass and the meaning's
pass (`FTm::turn`, with its `Ty::cast` of the test and `FTm::recast` of the
body) makes the kernel unfold `Loop::steps` on both sides, which recurses
`Loop::passes()` times. The pass bodies must meet by arguments, so the
write-out should spell the pass through the meaning's own helpers (or the
meaning should name a helper the write-out also names) before this is
routed. The value-metrics miss trace shows no miss for the item, so finding
the mismatching argument needs a probe theorem stating the two passes equal
at a variable state.
