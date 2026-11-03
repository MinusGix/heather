---
title: Take unifier approximations last, as named guesses, after forced solutions
status: closed
labels: [unification,inference,diagnostics]
area: language
created: 2026-11-02
updated: 2026-11-03
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

## Log

- 2026-11-03: Done. `unification::Guesses` names the unifier's guesses: an unsolved applied meta against a **longer** rigid spine (`?M(Nat) ≟ Pair2<Nat, Bool>` learning `?M := Pair2<Nat>`, and `?op(x, y) ≟ append<A>(x, y)` learning the type prefix), in the application congruence and in `flex_spine`. The equal-length alignment, a declared slot (`slot_pair`) and every first-order rule are decided and always run. An application's own reads (each inferred argument's type, then the expected type) run with `Guesses::Postpone`; when a slot is still open after them, `OwedChecks::guess` reads them again in order with the guesses taken and recorded, before the deferred arguments and instance obligations. Every other caller takes guesses where it meets them, as before. A refused argument whose read made the guess names it: "`M` was guessed as `Pair2<Nat, ·>` … give `M` as a λ". The acceptance probe `pick(r)` at `Result` elaborates since declared slots (`varies`), so the probes use `Pair2` (no slot); `fn PF(A) → Type` at the expected type now forces `M := PF` where the argument's guess used to win (`lib/_tests/std/core/type_constructor_tests.hthr`). The distinct-heads and spine-length checks are no longer guards: since unifier-lazy-delta they route to the δ step, so positional pairing of rigid spines happens only for one head at one length.
