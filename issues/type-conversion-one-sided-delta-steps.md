---
title: Type conversion unfolds one side to a head normal form in one run, not a step per round
status: closed
labels: [kernel,conversion,performance]
area: kernel
milestone: [none]
created: 2026-11-10
updated: 2026-11-10
---

Type conversion unfolded one side of a comparison a δ-step at a time
(`Conv::ty_w`, `crates/kernel/src/conv.rs`): when one type had a definition
at its head and the other did not, it took one `D::delta_ty` step, went
round the loop, and compared again. Each step re-entered the evaluator with
the type's pending spine, so a type that reaches its normal form after `n`
unfoldings replayed its spine `n` times. The term side has never done this:
a one-sided unfolding there is one transparent run to weak head normal form.

The shape that pays is a closed verdict used as a proof: `b.IsTrue()`
against `Unit` under `trivial`, where `b` is a long computation
(`docs/proof-patterns.md` §1). `IsTrue` unfolds to a `match` on `b`, which
is stuck until `b` is a constructor, so every δ-step of `b`'s head was a
round of the loop, each resuming a deep pending elimination. Found on the
x86 certificate's scan statements (`{p}_scanned_k`,
[[function-ir-scan-id-cost]]): the same scan stated as `scan(…) = True` by
`refl` cost a third of the kernel steps and a twentieth of the time of
`scan(…).IsTrue()` by `trivial`, which is the form every generator emits.

## What changed

The one-sided arms of `Conv::ty_w` call `D::delta_whnf_ty`, a new method of
the conversion domain: over values, `Eval::delta_whnf_ty` (one run); over
syntax, `delta_ty` repeated while the head has a definition. The verdict is
the same on every input: the loop took those same steps, one per round,
with nothing compared in between that could have accepted earlier (a type
with a definition at its head against one without is not yet comparable).
Both-sided unfolding is unchanged, since there the two sides may meet at a
common head before either is normal.

## Shape of the result

A closed verdict stated as `b.IsTrue()` costs what `b = True` does: the
evaluation of `b`, once. Measured on one scan statement of the scanner's
certificate (cloud box, width one): 342k kernel steps and 1.36 s before,
100k steps and 0.08 s after, which is what the `= True` form of the same
statement cost before the change.

Kernel round: the change is in the trusted conversion checker, held by
`scripts/test -p heather-kernel-lib --lib`, `scripts/bench --check` and the
whole-library gate.
