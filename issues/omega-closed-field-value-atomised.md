---
title: omega gives up on a record field when the call's arguments are closed
status: closed
labels: [omega,tactics,native]
area: tactics
created: 2026-10-29
updated: 2026-10-30
---

`omega` reads a field of a call as what the constructor put there
(docs/omega-measure-reduction-design.md §10–§12), but only while that value
stays stuck. When the call's arguments are closed, the bounded whnf in
`field_as_put_within` (crates/elab/src/omega_cert.rs) runs on into the
field's own computation, runs out of its 64-step budget, and the whole
projection falls back to one opaque atom. Two fields of the same record
then share nothing.

Probe on master 4f0ac27 ([[proof-patterns-audit-2026-10]]):

```
fn lay(n: Nat) → Nat { List::range(n).map(λ i => i * i).len() }
record Lay { size: Nat, cap: Nat }
fn Lay::of(n: Nat) → Lay { Lay(lay(n), lay(n) + 4) }
theorem at_var(n, a: Nat, h: a < Lay::of(n).size): a < Lay::of(n).cap { omega }   // ok
theorem at_lit(a: Nat, h: a < Lay::of(3).size): a < Lay::of(3).cap { omega }      // refused
```

`at_lit` is refused with atoms `[a, Lay::of(3).size, Lay::of(3).cap]`. A
field whose value is cheap (`idn(300)`) is read correctly, so the cut is the
budget, not closedness itself.

This is the shape of every native compiler proof: layouts and targets at a
literal program. Memory recorded the symptom as "omega over layout terms is
slow, use Nat step lemmas" (2026-10-25, S3.2); part of that cost is the
kernel converting the atoms' definitions, but part is this, which makes
`omega` give up on facts it can read.

## Wanted

Stop the field read at the projection's contractum: contract the projection
of the constructor and return the field's term as put, without evaluating
it. The value only has to be *spelled*, and its atom identity is decided
afterwards like any other subterm.

## Acceptance

- `at_lit` closes, as a probe in `lib/_tests/std/tactic/omega_tests.hthr`.
- A control: a record whose field is put as a computation `omega` cannot
  read still gets the stuck-call refusal it gets today.

## Resolution (2026-10-30)

The budget that ran out was not `field_as_put_within`'s but the one before
it: `projection_reduct` (`crates/elab/src/omega_cert.rs`) first asks for the
whole read's bounded weak head, which at closed arguments evaluates the
field on into `lay(3)`, and a spent budget returned from the function before
the read-as-put route ran. A spent budget now only skips that shortcut; the
receiver is unfolded as far as its pair and the field projected without δ,
as at a variable. Design: `docs/omega-measure-reduction-design.md` §14.
Probes `at_lit`, `at_lit_goal` and the control `closed_match_opaque` (a field
put as a `match` on the computation stays an atom) are in
`lib/_tests/std/tactic/omega_tests.hthr`.
