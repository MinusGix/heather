---
title: omega treats a measure applied to a constructor pattern as an opaque atom
status: closed
labels: [proofs,omega,elaboration]
created: 2026-09-05
updated: 2026-09-06
---



Found by the mutual-recursion design pass (2026-09-05,
docs/mutual-recursion-design.md §7), reproducing on a *single* `decreases`
declaration: `fn drop1(xs: List<Nat>) -> Nat decreases list_len(xs)` recursing
on the tail is refused — `list_len(t) < list_len(Cons(h, t))` "was not proved
automatically (`omega` got stuck: Omega could not spell a natural expression)".
`list_len(Cons(h, t))` is an opaque atom to the reflection rather than
`Succ(list_len(t))`, so the default closer fails on the single most common
measure obligation there is. Every existing `decreases` test discharges such
sites by hand (`merge`'s `succ_add_le`, `runs`'s `drop_eq_le`), which is why
it was invisible. Lever: reduce an atom to whnf (the value-domain probes of
`docs/…whnf…`, see [[elaborator-whnf-probes-on-computing-types]]) before
reflecting it, so a measure at a constructor pattern steps once. This is what
stands between the showcase parser and `omega`-only obligations.

## What it assumes from elsewhere
- **[[termination-measures]]** owns the obligation statement. Assumed here:
  only that the obligation is stated at the pattern-refined measure.

## Log

- 2026-09-06: Chartered (user, 2026-09-06) as one managed round, design then implementation: a bounded head reduction of the measure atom before reflection (not the general whnf, per elaborator-whnf-probes-on-computing-types), design at docs/omega-measure-reduction-design.md. Customer: the showcase parser's list-tail sites closing by omega alone.
- 2026-09-06: Design accepted (2026-09-06, docs/omega-measure-reduction-design.md). Premise corrected: there is no reducer/conversion gap — the reducer reaches Succ in six steps; what omega lacks is a SPELLING for the reduct's payload, and atoms intern by spelling. Verdict: bounded whnf at the atom fallback, kept only on an arithmetic head, leaves re-spelled by conversion against candidates built from the original term; omega_cert.rs only. Surfaced and filed: [[tier1-arm-binder-has-no-spelling]], [[lifted-obligation-refusal-reports-retry-error]].
- 2026-09-06: LANDED (2026-09-06, managed round; docs/omega-measure-reduction-design.md, §8 for what implementing corrected). Bounded whnf at omega's atom fallback, kept only on an arithmetic head; leaves named by conversion against candidates from the original spelling; depth 2 so two-successor measures close. The showcase parser group, merge, and the polymorphic evens/odds lose every hand discharge at a list tail; runs's drop_eq_le and gcd's mod_lt stay (genuine lemma sites). Suite 2426 -> 2464, 0 failed.
