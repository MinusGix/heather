---
title: A conditional simp law blocked at its first instance is not tried at the others
status: open
labels: [tactics,simp]
area: tactics
created: 2026-11-16
updated: 2026-11-16
---

Found adding the span read-over-write laws (`lib/native/runtime/rt_file.hthr`,
probes in `lib/_tests/native/runtime/rt_file_tests.hthr`).

`simp_only` takes a law's first instance in the goal; when that instance's
side condition is not discharged, the law is reported blocked and its other
instances are not tried. Three stores, the last over the first,

    xs.with_byte_within(n, i, v).with_byte_within(n, x, u).with_byte_within(n, i, t)

with `below: x.toNat() < i.toNat()` in scope, never reach their normal form
`xs.with_byte_within(n, x, u).with_byte_within(n, i, t)` under
`simp_only(List::with_byte_within_apart, List::with_byte_within_twice)`:
`with_byte_within_apart` first meets the outer pair (needing `i < x`, false)
and stops, though the inner pair is an instance whose condition is the local
`below` (`crates/elab/src/rewrite/simp.rs`, `fire`/`fire_at`). An ordered
commutation law, the usual way to normalise a run of writes, only works
where the first instance happens to be the one to swap.

Fix: on a blocked instance, go on to the next one (the walk's leaf callback
returns `Err(why)` and ends the search); report blocked only when no instance
fired.

Second gap from the same probes: `bv_omega` as a discharger did not prove
`toNat(x) = toNat(i) → False` from a local `apart: i.toNat() ≠ x.toNat()`;
`omega` did.
