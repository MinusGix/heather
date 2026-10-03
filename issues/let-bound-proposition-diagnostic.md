---
title: A let bound to a conjunction type reports an arity error on And
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-09-24
updated: 2026-09-28
---

## Scope

A `let` whose value is a type-level conjunction is refused with a diagnostic
that doesn't say what went wrong:

```text
let result = FetchedSteps(fetch, data, before, after) ∧ after.rip = next_rip(…);
error: `And` takes 2 argument(s), found 0
```

The same proposition written inline in a `match … as` motive elaborates. Found
building `lib/std/arch/x86_64/x86_64_fetched_code.hthr` (2026-09-24), and worked around
by inlining.

Decide whether a type-valued `let` is meant to work (it would read better in
long proofs that restate one proposition several times). If it isn't, the
diagnostic should say so rather than report an arity mismatch on `And`.

## Log

- 2026-09-28: Type-valued lets are supported. The reproducer exposed two gaps: a bare
  `And<P, Q>` in inference position was sent to the same-named constructor
  with no proof arguments, and an alias at a universe was not accepted as a
  named type in later annotations. Fully instantiated, unindexed type formers
  without value parameters now infer their ordinary type codes when no nullary
  constructor competes. Named aliases decode through the existing universe
  bridge; declaration type parameters retain precedence during field lowering.

  Regression coverage in `crates/elab/tests/logic.rs` exercises conjunction,
  disjunction and equivalence, explicit and inferred type annotations, a
  predicate application and an equation over an open carrier, reuse in a
  neutral dependent match motive, higher universes, constructor calls, nullary
  constructor ambiguity, function values, shadowing and invalid proofs/arity.
  `crates/elab/tests/let_and_blocks.rs` covers equality aliases, weakening at a
  literal match, binder precedence, declaration field scope and non-type aliases.
- 2026-09-28: CLOSED. The focused logic and block suites passed (50 tests). Final full
  `scripts/test` passed (3071 tests, 0 failures, 5 ignored), including the
  whole-library and native certificate acceptance checks. Type parameters,
  declared type names and builtins retain their existing precedence in type
  position; the new alias fallback does not change a record's declared fields.
  Documented the type-value inference rule and nullary-constructor annotation
  escape hatch in `docs/logic-connectives-design.md`.
