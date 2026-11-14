---
title: An inferred call's arguments see no expected type
status: closed
labels: [elaborator,inference]
area: language
created: 2026-11-14
updated: 2026-11-14
---

Split from [[surface-gaps-from-sha256-proof]] item 2. A call's expected type
now reaches an argument that would be inferred blind
(`application::propagate_expected`), but only when the call is itself
checked. A call that is inferred has no expected type to read:

    trans(cong_fn(λ (t: Sha256) => Mutated(t, 48), p), q)

`trans` is checked, so its result is known, but its first argument
`cong_fn(…)` is inferred (its domain `a = b` waits on `b`, which only `q`
fixes). Inside it the lambda body is inferred and `48` defaults to `Nat`.

**Why it is open:** the fix is to check an argument against a domain that
still holds metas (`?a = ?b`), letting the argument's own expected type flow
in with holes, and solve the holes from later arguments. This elaborator
solves each call in its own scratch world of metas, and an argument's
elaboration cannot yet see or write the caller's metas. Either the scratch
worlds nest, or the argument is postponed until a later argument fixes the
domain (Lean's postponement). Both are elaborator design choices for Minus.

**Workaround meanwhile:** put the argument whose domain is known first, or
ascribe the literal: `Mutated(t, (48: u64))`.

Probe: `literal_under_trans` in `lib/_tests/lang/expected_type_tests.hthr`
covers the checked case. A probe of this case should be added once it is
fixed.

## Resolution (2026-11-14)

Fixed for the case that met it: before an argument is inferred blind,
`application::propagate_expected` now reads, besides the expected type, the
type of every later argument that is a local variable or a `let` (its type
is known without elaborating anything), as that argument's own turn would.
`trans(cong_fn(λ t => Tagged(t, 48), h), finish)` checks its first argument
at `tagged48(a) = tagged48(b)`. Each local's read must settle its domain to
the local's type, or nothing is kept, as for the expected type.

Not covered: a later argument that has to be elaborated (a call), and a call
with no expected type whose first endpoint only the expected type would
say. Those still default; ascription (`(48: u64)`) is the spelling there.
Probes: `literal_before_local*`, `literal_before_let` in
`lib/_tests/lang/expected_type_tests.hthr`.
