---
title: A definition's own equations, one per branch, so a proof never restates the function
status: open
labels: [proofs,elaboration,native]
area: language
milestone: [lang-proof-modularity]
created: 2026-11-14
updated: 2026-11-14
---

Brief §5 of the optimizer side threads (2026-11-14): to use a function in a
proof it had to be restated. `Sha256::pushed` and `Sha256::padded` were
`push` and `pad` again with the test's bit as a parameter, equal by `refl`,
so that a case on the bit selected a branch.

## What is built (2026-11-14)

`crates/elab/src/branch_equations.rs`, elaborated after the declaration
(`DeclarationsMut::elab_branch_equations`).

- **Which declarations.** Every `fn` (not `meta`, not a `def` value, not
  `decreases`, `partial` or a `for` loop) whose body, after its `let`s, is a
  test on a `Bool`: `if P`, `if h: P`, `match b { True => …, False => … }`
  (an `_` arm standing for the other), `match h: b`. A body that calls the
  function again is skipped: its equations are its unfolding's
  ([[loop-invariant-rules]]'s `f::step`/`f::done`).
- **One equation per leaf.** An arm that is itself a test is split again,
  so `if a { … } else { if b { … } else { … } }` has `f::True`,
  `f::False::True`, `f::False::False`; at most sixteen leaves, else none.
- **Names** (Minus, 2026-11-14): by the arms taken, `f::True`/`f::False`,
  minted `f#True`, `f#False#True` and designated as `f::ext` is, so no
  name a module may declare is taken.
- **Statement.** `f(x̄) = arm` under one hypothesis per test, in the form
  the source wrote: `P` and `¬P` for `if P` (a `Nat` or word comparison
  stays one), `b = True`/`b = False` for a `Bool` (`if b` where `b` is not
  a proposition is read as the elaborator reads it, second). A condition
  that reads a `let` before it is stated with the `let`'s value. The arm is
  stated under the `let`s on the way to it and checked at the declaration's
  result type (an equation's sides are inferred, so a literal arm would
  take its default carrier otherwise).
- **Proof.** One `Bool::convoy_true`/`convoy_false` (a test with an
  equation) or `Bool::picked_true`/`picked_false` (one without) per test,
  chained by `trans`; the arm is the body's own, found proofs included. The
  checker sees each; one it refuses leaves `f` as it is, and a reference to
  the name reports the reason (`no branch equation …`).
- **As `simp` laws.** They are laws like any lemma: `simp_only(f::True)`
  fires where the hypothesis is in scope (simp design §10's side
  conditions).

Probes: `lib/_tests/std/core/branch_equations_tests.hthr`.

## Open

- `match` on an inductive other than `Bool`: `f::Zero`, `f::Succ` under
  `scrut = Succ(m)`, or with the scrutinee instantiated where it is a
  parameter.
- `f::True`/`f::False` beside `f::step`/`f::done` for a `decreases` body,
  so the two schemes are one (the loops' generator,
  `measure::step_equations`, would become this one after `f::unfold`).
- `unfold`/case analysis that picks the equation itself: a case on the
  condition that rewrites the call in each branch.
- Cost: every branching `fn` elaborates its equations eagerly. On the
  library (2026-11-14) about four hundred `fn`s qualify, and their
  equations are around one percent of the library's elaboration time; the
  largest are the lexer's `step_*` tables (read as `Bool` after the
  proposition reading fails, so elaborated twice) and record functions
  with long arms. Lazy generation, at a first reference, is the change if
  that grows.

## Log

- 2026-11-14: built; the SHA-256 stream proof
  (`lib/native/crypto/sha256_stream_agreement.hthr`) uses
  `Sha256::push::True`/`False`, `Sha256::pad::True`/`False` and
  `Sha256::put::True` in place of `pushed`, `padded`, `push_is`, `pad_is`
  and the hand convoy in `put_inside`. Found on the way: `omega` writes a
  hypothesis's name into generated source, so a primed name (`h'`) breaks
  its parse ("unterminated character literal"); the generator numbers its
  names instead (`h2`). The whole library re-elaborated with the generator
  on: every module passes. The SHA-256 rewrite is its own change
  (`/mnt/project-files/branch-equations/sha256-stream-by-branch-equations.patch`
  until it lands).
