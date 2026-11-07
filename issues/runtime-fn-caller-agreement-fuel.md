---
title: A runtime fn calling a dozen-arm callee is refused with a spelled True mismatch
status: closed
labels: [native,runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-07
updated: 2026-11-07
---

A `runtime fn` that calls a callee with about a dozen nested `match` arms is
refused, and the refusal does not say why. Found while assessing
[[self-hosted-lexer]]: a lexer's per-byte step is exactly such a callee.

## Reproduction

The files are in the project's `self-lexer/` folder (`full.hthr`); at
master `89ea8bb`:

- `class(b)`: a byte classifier, nine nested `match`es on `eq_bit` and
  `unsigned_lt_bit` of `BitVec(64)`, each arm a constant. Compiles and
  certifies through `compile-x86` (373 bytes).
- `begin(c)`, three arms, and `step_c(st, c)`, which calls `begin` in tail
  and non-tail position: both certify.
- `step_full(st, c)`: about a dozen arms over the state and class words, each
  a constant or `begin(c).add(k)`. Checks.
- `step(st, b) = step_full(st, class(b))` is refused:
  ``runtime fn step`: `step::agrees`: its body: an argument of type `True`
  where `El[0](…)` is expected``, the expected type spelled at length. Smaller
  callers of the same functions check (`step_c(st, class(b))`,
  `begin(class(b))`, a callee with half of `step_full`'s arms).

`--timings`: `step` ran 1.64M kernel steps before the refusal, past the
2^20 per-declaration fuel (`DEFAULT_FUEL`), so the likely cause is that
`step::agrees` is checked by evaluating the callees' programs and runs out of
fuel, and the out-of-fuel answer reaches the user as a mismatch. Unmeasured.
The callees themselves are costly: `class` took about 38 s, `step_full` about
62 s, most of it in the generator, which is
[[runtime-generator-link-cost]]'s measurement, not this issue's.

## Done when

A caller of a callee the default setup compiles is not refused for the
callee's size. A tool-sized step function (a lexer's, with tens of arms) is
the target. Where a budget is genuinely exceeded, the refusal names the
budget, not a spelled `True`/`El` mismatch.

## Log

- 2026-11-07: fixed. The callee's size reached the caller through
  `evaluable`: `f::agrees` checked `c.code.evaluable(…)` for every
  instance it linked (`Compile::part`) and `program_evaluable` of the whole
  program, and `evaluable`'s disjointness checks are quadratic in a
  function's nesting depth (about half the fuel for `class` alone; lowering
  is a tenth of that). But answering calls alike (`eval_answers`) uses only
  that each call fits its callee's arity, so it now takes
  `StructuredRegion::calls_fit` (linear), `Compile::part` asks for
  `calls_fit`, and `f::agrees` cites `program_fit_sources` over
  `program_calls_fit` (about a tenth of `program_evaluable` on `step`'s
  program, which ran out of fuel). `program_eval_sources` stays, through
  `program_evaluable_calls_fit`. The lexer's `step` checks; probe
  `byte_class`/`byte_class_pair` in `lib/_tests/native/runtime/runtime_tests.hthr`
  (fourteen arms, whose `program_evaluable` alone exceeds the fuel).
- The refusal: a host-built argument whose type comparison runs out of fuel
  is now refused naming the conversion budget, not as a spelled mismatch
  (`crates/elab/src/host.rs`, probe `budget_heavy_argument` in
  `lib/_tests/std/tactic/tactic_tests.hthr`).
- Not fixed here: `compile-x86` of `step` still runs out of fuel in the
  certificate's own `program_evaluable`, which the x86 proof needs
  (`eval_computes` reads the disjointness): [[function-ir-evaluable-quadratic]].
