---
title: Check the float specification against host binary32 results
status: open
labels: [mathematics,floating-point,testing]
area: mathematics
milestone: [math-float]
created: 2026-10-25
updated: 2026-10-25
---

The library's internal proofs check the executable rounding against
`RoundsTo`, but nothing checks `RoundsTo` and the special-value tables
against an independent IEEE implementation. A wrong tie rule, overflow
threshold or zero-sign clause that still satisfies uniqueness and
monotonicity would pass. The two specification bugs in Coq's primitive
floats were of exactly this kind (a typo in `leb`, inconsistent zero
classification; `docs/coq-hardware-floats-survey.md` §3, §5.4).

## The check

A small generator (a `scripts/` tool or a Rust bin, never a kernel change)
uses the host's binary32 unit (Rust `f32`, round to nearest even) to write a
probe file under `lib/_tests/std/num/float/`. The file holds theorems of the
form `Finite::add(a, b) = expected` proved by `refl`, with operands and
results written as `Finite(binary32())` values. The operands are chosen at
the edges:

- ties to even, and one ulp either side;
- the overflow threshold `Format::ovf` and the largest finite value;
- the subnormal boundary, gradual underflow, and the least subnormal;
- `x - x`, `fma` with exact-zero products, and `div` by signed zeros, for
  every IEEE §6.3 sign rule;
- NaN propagation and the invalid cases (`∞ - ∞`, `0·∞`, `0/0`).

The generated file is committed, so the suite does not run the generator;
regenerate it when the operations change. The expected values come from
hardware, so the probes are independent of the library's own reasoning.

## Why binary32

Binary32 evaluates by `refl` since [[kernel-wide-run-comparison]] and the
force-cache fixes. Rust's `f16` is not stable, and binary64 values are
larger. If binary64 evaluates within the rails, add a smaller binary64 set.

## Later customer

The native lane's SSE step forms, which must agree with the same vectors
(survey §4).

## Done when

The probe file covers every operation in `arith.hthr` at the edges above,
and the generator is documented beside it.
