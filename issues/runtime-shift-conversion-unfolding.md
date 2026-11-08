---
title: Runtime fn agreement unfolds large-count shifts
status: open
labels: [native,runtime-fn,elaborator,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

A `runtime fn` whose body puts a shift by a large count beside another shift
under one operation is refused by its generator: `a.shift_left(64).bor(b.shift_right(1))`,
`a.as_signed().shift_right(200).as_unsigned()`, and the signed shifts by 1000.
The note is "an argument's type could not be compared with the expected type
within the conversion budget": `Setup::compile`'s `rfl(f)` is checked against
`rt.meaning(world) = f`, and the conversion weak-head normalizes a reflected
value through `x.shift_left(64)` (recursive in its count, each step `init`
over 64 bits) instead of comparing the two `shift_left` applications
argument by argument.

Shifts by realistic counts compile, rotations among them
(`examples/x86-native/shifts.hthr`), and a lone large count does too
(`shifts_past.hthr`). Found in the i64 round 3
(docs/runtime-fn-setups-design.md §16.13).

## Directions

- Lazy δ in the elaborator's conversion: with the same constant at both
  heads, compare arguments before unfolding.
- Or the generator states `reflects` per parameter and closes it by a
  congruence the reflector already knows, not by `rfl(f)`.

## Acceptance

- `a.shift_left(64).bor(b.shift_right(1))` and an `i64` shift right by 1000
  compile through `compile-x86`.
