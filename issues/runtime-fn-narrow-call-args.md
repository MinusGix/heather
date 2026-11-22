---
title: Pass narrow words, Bools and enum fields across a runtime fn call
status: open
labels: [native, runtime-fn, compiler]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-21
updated: 2026-11-21
---

What docs/native/runtime-fn-setups-design.md §16.17 leaves refused after
several words crossed calls ([[function-ir-multi-word-calls]]):

- **A narrow word or a `Bool` passed to a call.** The callee reads the low
  bits of a 64-bit word, so the caller widens first: `Tm::call_args` emits a
  `Resize(w, 64)` before the call for each narrow argument and passes the
  fresh port, threading `next` past them; the proof is the entry's in reverse
  (`Ty::widen_by`). Refused today as "a call of a function whose parameters
  or result do not cross a call in 64-bit words" (`calls_digit` in
  `runtime_narrow_tests`).
- **A bit or a count among an enum's or a record's slots crossing a
  boundary.** A bit slot needs the width-one reading at its port (the `Bool`
  result's proof, per slot); a count is a `Nat`, whose word round-trips only
  below 2^64, so its contract needs a premise that it fits.
- **An enum as a record's field.** A record's field is one port (`Ty::Flat`
  is free of the type table), so an enum field would hold its tag alone; one
  with a payload waits for the record to hold the payload's slots inline,
  when a record and an enum both become "a code of several words".

## Done when

`calls_digit` compiles, and a record with an enum field is returned from
one runtime fn and matched in another.
