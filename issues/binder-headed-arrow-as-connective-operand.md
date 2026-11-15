---
title: A binder-headed function type cannot be a connective's left operand without extra parentheses
status: closed
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
- 2026-09-17: CLOSED. The `↔` rung is split out of `Parser::expr_rung` as
  `Parser::iff_rung`, and `Parser::ty`'s two binder-headed paths hand their
  curried Π to it through `Parser::iff_after_fn_type`, which declines while a
  codomain is being read (`Parser::no_iff`) exactly as `expr_rung` does. So
  `(a: A) → P(a) ↔ R` now parses as `((a: A) → P(a)) ↔ R`, checked against the
  `Iff<(a: A) → P(a), R>` hypothesis rather than against itself, and in a
  Type-valued *body* too — that route reaches the rung differently (the Π
  arrives as a `TyLit`, the plain arrow's as a `TyApp`), and all three
  spellings are pinned to one type.

  Nothing that parsed before parses differently: every position where a `↔`
  can follow a binder-headed Π was a parse error, the type-argument slot
  included — there the speculation rewind fires and then fails anyway.
  Preserved and pinned: `P → Q ↔ R` is `(P → Q) ↔ R`; the bracketed
  `(a: A) → (P(a) ↔ R)` stays the other reading; `↔` still does not chain;
  and a binder-headed **codomain** still leaves the `↔` to the outer arrow, so
  `P → (a: A) → Q(a) ↔ R` is `(P → (a: A) → Q(a)) ↔ R`.

  **Scope is unchanged, deliberately.** The Π is built — binders *and*
  codomain — before the `↔` applies, so `(a: A) → P(a) ↔ Q(a)` still reports
  `unbound name a`. That is [[iff-in-type-valued-body]]'s "do not silently
  change arrow/Iff precedence"; what moved is only that the spelling is now a
  *reading* rather than a parse error, and the parenthesized
  `(a: A) → (P(a) ↔ Q(a))` remains how you say the other thing.

  On the acceptance's implicit-binder clause: the parser treats `{a: A} → …`
  identically — the same `iff_after_fn_type` call sits on that path — but
  `{a: A} → P(a)` in a result-type position is refused *before* the `↔` is
  reached, by the separate restriction [[implicit-binders-in-function-types]]
  owns ("implicit binders take effect in parameter types, `let` annotations,
  field types, and lambdas"). Verified on the parent commit that the same
  spelling without any `↔` is refused with the same message, so nothing here
  is what blocks it. A second, unrelated gap turned up beside it and is NOT
  fixed here: `({a: A} → P(a)) ↔ R` is `parse error: expected `}`, found
  Colon` — a parenthesized implicit binder, also pre-existing on the parent
  commit, and owned by that issue rather than this one.

  Tests: `a_binder_headed_function_type_reaches_the_iff_rung` (shape) in
  `crates/syntax/src/parser.rs` and
  `a_binder_headed_function_type_can_be_the_iff_operand` (meaning, with the
  three negative controls above) in `crates/elab/tests/logic.rs`.
  `docs/library/logic-connectives-design.md` §4.2 records the rule.
