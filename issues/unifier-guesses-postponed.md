---
title: Take unifier approximations last, as named guesses, after forced solutions
status: open
labels: [unification,inference,diagnostics]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Three rules inside `unify_tm`'s application case are approximations, not
consequences of the equation: peeling a rigid spine's type prefix for an
applied meta (`?op(x, y)` learns `append<A>`), the last-argument abstraction
for `?M(A) ≟ F<B, A>`, and positional pairing of two rigid spines (fenced
today by the length and head guards that [[constrained-predicate-expected-type]]
and [[and-at-match-predicate-implicit-level-mismatch]] added). Mixed into
congruence, a guess is taken as early as a forced solution and, with first
write wins, blocks the right one.

## Proposal (P2 of docs/elaborator-principles-survey.md)

Decided rules first (identity-renaming pattern, same rigid head, `El ?A`),
δ at head mismatch ([[unifier-lazy-delta]]), and approximations last: a named
final step that runs only for slots still `Unsolved` after the expected type
and deferred arguments, records which guess it made, and is reported by name
when the call is later refused. The distinct-heads and spine-length guards
then disappear: positional pairing only ever happens for the same head.

## Acceptance

- [[applied-meta-approximation-diagnostics]]'s `pick(r)` message names the
  guess (`M := Result<Nat, ·>`, last argument abstracted).
- The guard probes of the issues above still refuse or now elaborate, never
  take a wrong-typed solution.

After [[unifier-lazy-delta]].
