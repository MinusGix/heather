---
title: Pass an enum as a record's field, and export wide results to C
status: open
labels: [native, runtime-fn, compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-21
updated: 2026-11-21
---

What docs/native/runtime-fn-setups-design.md §16.17 left refused after
several words crossed calls ([[function-ir-multi-word-calls]]), and where
each stands after §16.18.

- **A narrow word or a `Bool` passed to a call.** Done (§16.18): the caller
  widens with `Resize(w, 64)` into a fresh port (`Tm::send_slots`);
  `calls_digit` in `runtime_narrow_tests` compiles.
- **A bit among an enum's or a record's slots crossing a boundary.** Done
  (§16.18): a slot is a word, a narrow word or a bit (`Ty::Slot`), in all
  four directions; probes in `runtime_slots_tests`.
- **A record or enum parameter in a function lent spans.** Done (§16.18):
  `f::agrees_over` at the value (`token_peek`, `flag_peek`).
- **A count among the slots.** Still refused: a `Nat` round-trips through a
  word only below 2^64, so its contract needs a premise that it fits, which
  no caller states.
- **An enum as a record's field.** Still refused. `Ty::Flat` is free of the
  type table, since the table's records are built from it; the table splits
  into enums first (payload slots only) and records over them, a record's
  enum field crossing as the enum's words inline.
- **A result of more than two words exported to C.** Still refused by
  `compile-x86` (`runtime_shape`). System V returns such a structure
  through a pointer the caller passes in RDI and expects back in RAX; it
  needs an entry that shifts the arguments, calls, stores the answer
  registers through the pointer, and a machine contract that memory changes
  exactly there, proved once for every word count.
- **Records with two narrow fields side by side at a C boundary.** Refused
  by `compile-x86` on purpose: C packs them into one eightbyte, one
  register, where a record here crosses a word a field (`Ty::slots_share`).
  Passing such a record in C's layout would unpack each eightbyte with
  shifts at the entry and pack them on return.

## Done when

A record with an enum field is returned from one runtime fn and matched in
another, and a record of three words is returned to a C caller.
