---
title: Generic datareprs over a value-parameter telescope
status: open
labels: [datarepr]
area: heather-in-heather
created: 2026-11-08
updated: 2026-11-08
---

`datarepr N for SInt(64)` works since [[sint-native-lowering]]
(`valparam_spec_view`, crates/elab/src/datarepr.rs): a spec type that is an
inductive applied to closed value arguments is monomorphised at those
arguments, keyed `(tag, "64")` in the registry, and the host's `Repr`
request finds it from `SInt(64)`. `sint.hthr` therefore states one repr per
width (`I8`…`I64`).

Wanted: one repr over the telescope, `datarepr I for (n: Nat) SInt(n) { R
:= BitVec(n), … }`, its registry key the family, its `abs`/`emb` taking `n`,
and `Repr` answering an applied instance at any width (neutral too). The
`runtime` generator would then read the carrier's width off the instance.

## Log

- 2026-11-08: 2026-11-08: deferred in i64 round 4: the runtime generator would only read a width off the family once a narrow SInt can be held (runtime-repr-narrow-words, itself waiting on function-ir-narrow-arithmetic at S4), so this moves with that issue rather than alone.
