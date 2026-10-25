---
title: An argument that mismatches an implicit-bearing parameter reaches the kernel
status: open
labels: [elaborator, diagnostics]
area: language
created: 2026-10-24
updated: 2026-10-24
---

Found while giving the rational refusals their reasons
([[library-tests-as-theorems]], round 2). The elaborator accepts a call whose
explicit argument has the wrong type when the parameter's type mentions an
implicit, and the kernel is what refuses it:

```heather
import logic; import bool; import nat; import int; import algebra; import omega; import rat;
theorem f({a: Rat}, hz: 0 <= a): a <= a { a.le_refl() }
theorem bad(a: Rat): a <= a { f(a.le_refl()) }
```

`bad` is refused with `the kernel rejected `bad`: NotConvertible`. The same
argument written where nothing is implicit, `theorem bad(z: Rat): 0 <= z {
z.le_refl() }`, is refused by the elaborator as a mismatch (`this has type
Le(z, z), but Le(ofInt(OfNat(0)), z) is expected here`), and so is the call
when the expected type does not also determine `a` (`f({a, b}, h: a <= b, hz:
0 <= b): a <= b` called as `f(h, b.le_refl())`). At `Nat` the same shape is
refused by the elaborator, because `0 <= b` computes to `True`.

Nothing unsound gets through (the kernel refuses), but the diagnostic is the
kernel's, with no span inside the call and no types, and the elaborator
handed the kernel a term it should have known was wrong. A guess at the
cause, not checked: the implicit is solved from the expected type first, and
the argument's own check is skipped or its failure dropped once inference
has an assignment.

The library tests pin the current behaviour as `Refusal::Kernel`
(`crates/elab/tests/lib_std_rat.rs::scaling_needs_a_sign`,
`lib_std_creal.rs`'s `mul_pos` case,
`lib_std_ordered_field.rs::inverse_sign_of_negative`); a fix turns those into
`Refusal::Mismatch`, which is the test telling you it worked.

Separate from this: most `CReal` vacuity controls are also kernel refusals,
with the message `the type of this expression does not convert to the type
expected here (neither has a surface spelling)`. Those look like the
elaborator's conversion leaving a sequence comparison to the kernel, which is
by design; check that before folding them in here.
