---
title: Sign extension and signed division in rt
status: open
labels: [native, runtime-fn]
area: heather-in-heather
milestone: [nh-front]
created: 2026-11-08
updated: 2026-11-08
---

Of [[sint-native-lowering]]'s four signed operations, `lt_bit` (`Slt`,
`JL`) and `shift_right` (`Ashr`, `SAR`) reflect since the `datarepr`
round (docs/runtime-fn-setups-design.md §16.13). The other two have no `rt`
op to land on:

- **`SInt::extend` (`MOVSX`)** unfolds to `BitVec::sign_extend`, which the
  reflector does not know. Wanted: `rt` `Sext(w, extra)` with its meaning
  `BitVec::sign_extend`, a FunctionIR lowering (no signed `Resize` exists;
  `Resize` is `ofNat ∘ toNat`, §16.12), and the law `Tm::lower_sound`'s
  case needs.
- **`SInt::div`/`rem` (`IDIV`)** unfold to `BitVec::sdiv`/`srem`; `rt` has
  no division at all, signed or not (`Udiv` is missing too). The laws are in
  `bitvec_div.hthr` (`udivrem_spec`, `sdiv_srem_toInt`); the meaning at a
  zero divisor and at `MIN / -1` is whatever `BitVec::sdiv` says, so a
  lowering to `IDIV` must guard both (x86 faults on them).

Neither reaches the x86 back end yet in any case: S4 refuses shifts and
`Resize` ([[function-ir-x86-shift-legalization]]).
