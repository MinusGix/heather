---
title: Runtime fn agreement unfolds large-count shifts
status: open
labels: [native,runtime-fn,elaborator,performance]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-10
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
(docs/native/runtime-fn-setups-design.md §16.13).

## Directions

- Lazy δ in the elaborator's conversion: with the same constant at both
  heads, compare arguments before unfolding.
- Or the generator states `reflects` per parameter and closes it by a
  congruence the reflector already knows, not by `rfl(f)`.

## Acceptance

- `a.shift_left(64).bor(b.shift_right(1))` and an `i64` shift right by 1000
  compile through `compile-x86`.

## Log

- 2026-11-10: From the emission round
  ([[native-function-emission-one-statement]]): the same cost from the other
  side. `rt_lower_tests::spread_agrees` (eight primitives over one open
  word, among them an arithmetic shift by 60) spends about 0.85M of its 2^20
  steps, nearly all in `BitVec::snoc` under `tail_bits`: the shifts of an
  open 64-bit vector, a bit at a time, on both sides of the conversion. It
  is the dearest agreement in the library's tests and sits at four fifths of
  the budget.

  That margin is held up by an accident. The lowering checks each operand's
  type code with `Ty::check`, whose `Nat::equation` walks both widths a
  successor at a time, and that walk forces the width thunks the bit-vector
  recursions then share. Deciding the check by `Ty::same` instead (no walk,
  no proof kept: it would take the equation's share, about a sixth, off
  every function's emission and made the small agreement probes two to three
  times cheaper) leaves the widths as runs whose predecessors are made fresh
  by each fold, the two sides share less, and `spread_agrees` runs out of
  fuel with `snoc` at 0.77M and climbing (0.54M with the walk). Deciding the
  same `agrees` by `equation` restored the count exactly, so it is the walk
  and not the proof. The change was not shipped; it is saved as a diff in the
  round's notes and is a few dozen lines (`Ty::agrees`, `agrees_sound`,
  `agrees_then`).

  So the fix here pays twice: once shifts of an open word are compared
  without being unfolded (or folded by the evaluator), the lowering's checks
  can stop building equations.
