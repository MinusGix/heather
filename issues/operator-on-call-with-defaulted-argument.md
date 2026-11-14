---
title: An operator whose operand is a call with a defaulted argument finds no meaning
status: closed
labels: [elaboration,operators,named-arguments,ergonomics]
area: language
created: 2026-11-13
updated: 2026-11-13
---

```heather
fn vat32({n: Nat}, v: [u32; n], i: u64, inside: i.toNat() < n := bv_omega) → u32 { vector_get(v, i.toNat(), 0) }

fn p1(v: [u32; 64], j: u64, h: j < 48) → u32 { vat32(v, j + 14) + vat32(v, j) }
// `+` has no meaning here: no constraint binder named it …, no `designation + at …` covers this carrier
fn p3(v: [u32; 64], j: u64, h: j < 48) → u32 { let a = vat32(v, j + 14); a + vat32(v, j) }
// ok
```

The callee's result type is written (`u32`) and the expected type is known, yet `+` is refused where its left operand is a call that leaves a defaulted parameter out. Bound by a `let` first, the same call is fine. So the operand's type is not read when the designation is chosen (a call with a default to fill seems to have no type on the quick path).

Found 2026-11-13 in PR #551's thread, where an indexed read carries its bound as a defaulted proof: SHA-256's `end` adds two of them (`vector_at(s.hash, i) + vector_at(s.working, i)`).

## Done when

`p1` checks, with a probe in `lib/_tests`.

## Log

- 2026-11-13: Filed. Scratch reproduction in `/mnt/project-files/wip/ix2-ext-probe.hthr`'s history; the two functions above are the whole of it.
- 2026-11-13: Two causes, both fixed on PR #607. A defaulted parameter is recorded as an implicit one, and one that no other parameter's type mentions made the call "deferred for a result-only implicit" (`Callables::call_defers_for_result_only`), so the operator's carrier probe passed over it: a parameter with a default is now no reason to wait for an expected type. And a carrier probe whose operand fails only because a search in it wants a goal slot the attempt has not reserved lost the restart request to its own rollback: `op_carrier_head` makes the request again outside the probe, so the declaration restarts with the slot. Probe: `two_below` in `lib/_tests/std/tactic/bitvec_omega_tests.hthr`.
