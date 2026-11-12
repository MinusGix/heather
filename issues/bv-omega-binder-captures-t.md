---
title: bv_omega's generated proof binds t and captures a user variable of that name
status: closed
labels: [proofs,bitvec,metaprogramming]
created: 2026-11-12
updated: 2026-11-12
area: tactics
---

Found writing a probe for [[runtime-measured-reader-heavy-callee]] (2026-11-12). A `decreases` obligation closed by `bv_omega` in a function whose counter is named `t`:

```heather
runtime fn probe_find(ctx: List<BitVec(8)>, cn, t: BitVec(64)) → BitVec(64) decreases BitVec::ofNat(64).sub(t).toNat() {
    match h: t.unsigned_lt_bit(BitVec::ofNat(64)) {
        False => t,
        True => probe_find(ctx, cn, t.add(BitVec::ofNat(1))),
    }
    on ?dec1 := { let below = bitvec_omega::unsigned_true(64, t, BitVec::ofNat(64), h); bv_omega };
}
```

> error: could not infer the implicit argument `n` of `bitvec::BitVec::toNat`
>   generated `bv_omega` proof: { … `@cong(λ (t: Nat) => nat::Nat::add(nat::Nat::mul(1, (bitvec::BitVec::toNat(t))), t), nat::Nat::add(0, 1), 1, refl)` … }

The proof `bv_omega` writes binds a variable it calls `t` (the `cong` motives in `__bv_mq…`/`__bv_mp…`), and the atom it abstracts around, `BitVec::toNat(t)`, mentions the user's `t`. Inside the motive the user's word is shadowed by the tactic's `Nat`, and `toNat(t)` no longer types. Renaming the counter to `i` is the whole fix on the user's side, and nothing in the message says so.

It is the tactic's text that captures, so the same holds for any name the generated proof binds (`__bv_…` names cannot clash; `t` can).

## Scope

The motive's binder gets a name no user term can hold (`__bv_t`, as the rest of the generated proof is named), in `bv_omega`'s proof writer and anywhere else a tactic's printed proof binds a plain name around user terms; a probe with a counter named `t`.

## Done when

The function above checks as written.

## Log

- 2026-11-12: Done: the generated cong motives bind __bv_t. Probe named_t in lib/_tests/std/tactic/bitvec_omega_tests.hthr (and count_up_t, a decreases loop over a counter named t).
