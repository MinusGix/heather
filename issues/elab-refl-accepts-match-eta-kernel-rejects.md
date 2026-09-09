---
title: Elaborator accepts `refl` for `add(x, OfNat(0)) = x` at open `x`; the kernel rejects it
status: open
labels: [elab,kernel,conversion,diagnostics]
created: 2026-09-09
updated: 2026-09-09
---

Found while landing [[int-arithmetic-over-nat-primitives]]. With `int::add`
defined by `match a { OfNat(m) => match b { OfNat(n) => OfNat(m + n), … },
NegSucc(m) => match b { OfNat(n) => subNatNat(n, Succ(m)), … } }`:

```
import int;
theorem open_right_unit(x: Int): int::add(x, OfNat(0)) = x { refl }
```

elaborates and is then refused by the kernel (`the kernel rejected
`open_right_unit`: NotConvertible`). The same equation given as a hypothesis
in checking position (`h: a <= b` against `add(a, OfNat(0)) <= add(b,
OfNat(0))`) is refused by the elaborator itself, so the permissive path is
specific to `refl`'s conversion check. The shape suggests the elaborator
identifies a `match` on a neutral scrutinee whose arms each rebuild the
scrutinee's constructor (`OfNat(m + 0) ⇝ OfNat(m)`, `subNatNat(0, Succ(m)) ⇝
NegSucc(m)`) with the scrutinee — a match-eta the kernel does not have.
Three library proofs (`add_le_mono_r`, `mul_add_distr`, the `CommMonoid<Int>`
right unit) hit this during the round: each elaborated and failed only in the
kernel, with the least helpful diagnostic the pipeline has.

Wanted: either the elaborator's conversion loses the rule (the kernel is the
authority: docs/delam has no match-eta) or the discrepancy is documented as a
deliberate elaboration-time convenience whose failures are reported at the
`refl` with the two sides shown, not as a kernel rejection of the whole
declaration.

## What it assumes from elsewhere

- The kernel's conversion (`crates/kernel/DESIGN.md`) is the definition of
  definitional equality; the elaborator may be *stricter*, never looser.
