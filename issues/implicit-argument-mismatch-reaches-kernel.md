---
title: An argument that mismatches an implicit-bearing parameter reaches the kernel
status: closed
labels: [elaborator, diagnostics]
code: crates/elab/src/application.rs
area: language
created: 2026-10-24
updated: 2026-10-25
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

## Resolution (2026-10-25)

**Cause.** The guess was close, and the gap was wider than the title. A
checked argument is compared with its domain by being checked; checking
records a candidate (`note_check_mismatch`) that the gate's refusal is
reported at. An argument whose domain still mentions an unsolved implicit is
*inferred* instead, and its type only teaches the call's metas
(`unify_application_argument_type`), a unification that is learn-only:
failure is silent. Nothing compared the argument's type with the domain
under the final solutions, so nothing recorded a site, and the kernel's
refusal came back bare. That holds whoever solves the implicit: the expected
type (the filed case), or the mismatching argument itself (`let r = f(h); r`
with `f({a: Nat}, h: 0 = a)` and `h: a = a`, no expected type at all). Every
route that infers an argument took it: the Π walk, arguments spilled onto a
callable result, and the deferred-argument fallbacks in `retry_obligations`.

**Fix.** `OwedChecks` (`crates/elab/src/application.rs`). Learning from an
inferred argument's type now goes through `OwedChecks::learn`, which keeps
the (domain, type) pair; the call's discharge hands each pair, the domain
under the final solutions, to `note_argument_mismatch`, which records the
same candidate checking does. Recording, not probing, so a declaration the
gate accepts pays one substitution per inferred argument and no conversion.
A call abandoned before its discharge (a re-plan, an error) records nothing.
`note_argument_mismatch` is a required trait method, and the learn-only
unification's one remaining direct call is a collection literal's counted
length, before that literal is itself checked.

Of the pinned refusals, `scaling_needs_a_sign` and `inverse_sign_of_negative`
are now `Refusal::Mismatch`. `CReal::mul_pos` at `hx: 0 <= x` is reported at
`hx` with its type, but `0 < x` at `CReal` has no surface spelling, so the
note is located, not a mismatch.

The `CReal` vacuity controls of the last paragraph are the by-design case:
their notes are already located at the site (the gate decides the
conversion, the probe finds where), and only the display is missing.

Tests: `crates/elab/tests/check_reports_mismatch.rs`
(`an_inferred_argument_at_an_implicit_bearing_parameter_reports_at_the_argument`:
expected-type and argument-solved implicits, a variable and a call, a curried
parameter, an `@` call, a receiver, a named argument, a constructor field, an
open element type; each was the kernel's refusal before; and its control),
and the unit test
`application::tests::an_inferred_argument_owes_its_comparison_at_the_discharge`.
Three existing tests changed their pin to the new, earlier site: a wrong
callback to `Result::map` and a swapped `@` dictionary (both bare kernel
refusals before, now spelled mismatches at the argument), and `q.trans(p)`,
now reported at `p` rather than at the result.

