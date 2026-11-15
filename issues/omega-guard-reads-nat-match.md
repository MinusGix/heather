---
title: omega's guard round splits a stuck Nat match in a guard
status: open
labels: [omega,tactics,proofs]
area: tactics
milestone: [tac-arith]
created: 2026-10-30
updated: 2026-10-30
---

`omega`'s guard round ([[omega-reads-bool-guards]], design §17 of
`docs/tactics/omega-measure-reduction-design.md`) reads `&&`, `||`, `!`, `leb` and
Bool definitions, but a stuck `match` inside a guard is bound and left
alone. `Format::canonical`'s least-exponent test is one:

```heather
let normal = match bexp { Zero => True, Succ(_) => F.half().leb(mag) };
```

so `canonical_elim`'s disjunct `bexp = 0 ∨ F.half() <= mag` still comes
from `reflects_elim`, and every client that wants `F.half() <= mag` at a
nonzero exponent (`Finite::normal_mag`, `Finite::bexp_zero_of_small`,
window.hthr) matches on it by hand.

Wanted: a guard part `match n { Zero => x, Succ(_) => y }` at `Nat` with a
neutral scrutinee is split into `n = 0` (and `x`) and `0 < n` (and `y`),
the way §16 splits a truncated subtraction: one rule in omega.hthr whose
continuations see the arm's Bool at the case, bounded like the
subtraction splits. The kernel spelling of the match is an eliminator, so
the rule takes the match's motive and arms as implicits read off the
evidence, as the other guard rules do; whether the unifier solves those is
the first question.

Acceptance: `omega(f.ok, nz)` gives `F.half() <= f.mag` from
`nz: 0 < f.bexp`; `canonical_elim`'s third conjunct is `omega`-provable as
an `∨` goal or the clients above drop their `match c.right.right.left`; a
probe and a control in `lib/_tests/std/tactic/omega_tests.hthr`.

## Log

- 2026-11-05: gardener: cites a file it shares with [[frontend-roadmap]] (`docs/tactics/omega-measure-reduction-design.md`); [[lifted-obligation-refusal-reports-retry-error]] (`docs/tactics/omega-measure-reduction-design.md`); [[review-lint-redundant-motive-on-generated]] (`lib/_tests/std/tactic/omega_tests.hthr`).
