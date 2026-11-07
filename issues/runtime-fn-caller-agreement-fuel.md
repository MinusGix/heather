---
title: A runtime fn calling a dozen-arm callee is refused with a spelled True mismatch
status: open
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
