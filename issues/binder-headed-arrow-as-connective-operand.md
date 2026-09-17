---
title: A binder-headed function type cannot be a connective's left operand without extra parentheses
status: open
labels: [frontend,syntax,parser]
created: 2026-09-17
updated: 2026-09-17
---

`↔` is looser than `→`, so `(a: A) → P(a) ↔ R` should be
`((a: A) → P(a)) ↔ R` — the same reading `P → Q ↔ R` already gets. It is not a
wrong reading; it is a **parse error**:

```heather
theorem t<A>(P: A → Type, R: Type, h: Iff<(a: A) → P(a), R>): (a: A) → P(a) ↔ R { h }
```

```text
parse error: expected `{`, found Iff
```

The extra parentheses work and are what `crates/elab/tests/logic.rs` already
writes (`((n: Nat) -> P) ↔ Q`):

```heather
theorem t<A>(P: A → Type, R: Type, h: Iff<(a: A) → P(a), R>): ((a: A) → P(a)) ↔ R { h }
```

## Where it comes from

`Parser::ty`'s **binder-group** path — `(x: A) -> B` — builds the curried Π and
`return`s it. Every other route into a type reaches `Parser::expr`, which is
where the `↔` rung lives, so only the binder-headed spelling has no rung above
it. The non-dependent arrow does not have the problem: `P → Q ↔ R` goes through
`expr_no_iff`'s arrow branch and comes back to `expr`'s `↔`.

`∧`/`∨` do not show it because they bind **tighter** than `→`:
`(a: A) → P(a) ∧ R` parses, as `(a: A) → (P(a) ∧ R)`, which is the intended
reading and needs nothing above the Π. Only a rung looser than the arrow is
affected, and `↔` is the only one.

## Acceptance

- `(a: A) → P(a) ↔ R` parses as `((a: A) → P(a)) ↔ R` — checked against the
  named-constructor hypothesis `Iff<(a: A) → P(a), R>`, not against itself.
- The implicit-binder spelling `{a: A} → P(a) ↔ R` gets the same treatment, or
  a recorded reason why not.
- The diagnostic, if the case is instead declined on purpose, says what to
  write; ``expected `{`, found Iff`` names the theorem body's brace and points
  nowhere useful.
- Existing precedence untouched: `P → Q ↔ R` is `(P → Q) ↔ R`, and
  `(a: A) → (P(a) ↔ R)` stays the bracketed reading
  ([[iff-in-type-valued-body]]).

## What it assumes from elsewhere

- **[[iff-in-type-valued-body]]** owns the *bracketed* half of the same corner
  and closed it 2026-09-17. Assumed here: only that a bracket lifts the
  codomain's `↔` restriction, which is what makes the parenthesized escape
  hatch above work at all.
- **[[std-logic-module]]** owns `↔` and its precedence. Assumed here: only that
  `↔` is looser than `→` and non-associative.

## Log

- 2026-09-17: Filed from the [[iff-in-type-valued-body]] round, which hit it
  writing that issue's negative control and reached for the non-dependent
  arrow instead. Confirmed pre-existing by rebuilding the parent commit.
