---
title: Elaborator accepts `refl` for `add(x, OfNat(0)) = x` at open `x`; the kernel rejects it
status: closed
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

## Log

- 2026-09-09: Resolved as a *reporting* change; the premise was wrong in an
instructive way. There is no match-eta in the elaborator's conversion, because
`refl` never reaches a conversion: `ExprKind::Refl` in `check_form`
(`crates/elab/src/expr.rs`) reads the expected `Id`, emits `Refl(lhs)` and
compares the two sides **never** — so every false equation under `refl` went
to the kernel unexamined, and `n = Succ(n)` was the same defect wearing a
smaller hat. The kernel keeps the rule it has, and the elaborator keeps the
rule it never had. What changed is the message: `Elaborator::note_refl_mismatch`
records — never raises — a budgeted conversion verdict at each written `refl`,
and the gate reads it only when the gate itself rejects with `NotConvertible`.
Unlike `note_check_mismatch`'s note it does not *replace* the gate's report:
`NotConvertible` at a named declaration is what the certifying pipeline's
mutation controls read, and their `refl` pins have sides no display can spell.
The verdict and class stay, the span moves to the `refl`, and the two sides are
appended when both spell cleanly and differently. The filed case now reads
"the kernel rejected `open_right_unit`: NotConvertible. `refl` needs both sides
to be definitionally equal, but `add(x, OfNat(0))` and `x` are not", carets
under the `refl`.
