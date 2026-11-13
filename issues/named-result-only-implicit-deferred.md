---
title: A call that names its result-only implicit is still deferred, so a numeral beside it is read as Nat
status: closed
labels: [elaboration, implicits, numerals]
area: language
created: 2026-11-13
updated: 2026-11-13
---

Found writing probes for [[bv-omega-masked-word-bound]]. In an inference
position, a numeral beside a word whose width is named was read as `Nat`:

```heather
theorem t(): (BitVec::ofNat(37, n := 64) & 15).toNat() = 5 { refl }
// error: this has type `Nat`, but `BitVec(64)` is expected here  (at `15`)
```

The same with `.band(15)` and `BitVec::band(…, 15)`; in a checking position
(`fn f() → BitVec(64) { BitVec::ofNat(37, n := 64) & 15 }`) it worked.

## Cause

`BitVec::ofNat({n: Nat}, x: Nat)`'s `n` occurs in no explicit parameter's
type, so `Callables::call_defers_for_result_only` called every
`BitVec::ofNat(…)` argument checking-only: it waits for the expected type
that is the only other evidence for `n`. The test looked at the callee's
declaration and the positional count, never at the named arguments, so
`n := 64` changed nothing. Deferred, the receiver left `band`'s width
unsolved while `15` was elaborated, and the numeral took `Nat`.

## Fix

The walk returns *which* implicits are result-only (memoized per
declaration as before), and a call defers only when one of them is not
named. Naming them is what `@name(…)` does for all parameters, which was
already a guard.

Probes: `lib/_tests/std/bitvec/bitwise_symbols_tests.hthr` (operator, method,
qualified call, open width, checking position, and the unnamed negative
control) and `mask_literal_numeral` in
`lib/_tests/std/tactic/bitvec_omega_tests.hthr`.

## Log

- 2026-11-13: filed and fixed.
