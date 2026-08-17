---
title: "`∃`/`∀` notation cannot appear in a type-argument slot, even parenthesized"
status: open
labels: [frontend,syntax,parser,stdlib]
created: 2026-08-16
updated: 2026-08-16
---

```heather
theorem le_iff_exists_add(n, m: Nat): Iff<Le(n, m), ∃ (k: Nat), add(n, k) = m> { … }
```

does not parse, and neither does the parenthesized
`Iff<Le(n, m), (∃ (k: Nat), add(n, k) = m)>`. Both were run (2026-08-16); the
errors are different and that is the whole content of this issue.

**Unparenthesized** the failure is expected and arguably correct: the
quantifier's own `,` — the separator between binder and body — is also the
type-argument separator, so `∃ (k: Nat), add(n, k) = m` inside `Iff<…>` is
genuinely ambiguous, and the parser reads the `,` as ending the argument.

**Parenthesized** it is not. `(∃ (k: Nat), …)` reports `expected parameter
name, found LParen`: a parenthesized quantifier is not something `Parser::ty`
can read at all, so the escape hatch that resolves the ambiguity everywhere
else is absent here. That is the bug — the workaround for the first failure
should work, and does not.

The landing spelling is the **call form**, which is fine and is what wave 0
shipped:

```heather
Iff<Le(n, m), Exists(λ (k: Nat) => add(n, k) = m)>
```

so `lib/std/nat.hthr`'s `le_iff_exists_add` is written that way and nothing is
blocked. What is lost is that the notation and the call spelling are supposed
to be interchangeable ([[std-logic-module]]'s claim), and here they are not.

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `Exists` and the `∃`/`∀` notation. Assumed
  here: only that the notation is meant to be a spelling of the call, usable
  wherever the call is.
- **[[comparison-inside-type-arguments]]** is the sibling gap in the same slot,
  from the same round, and probably shares a fix: both are "the type-argument
  grammar admits less than the type grammar".

## Log

- 2026-08-16: Filed from the [[nat-order-kit]] round (`docs/nat-order-design.md`
  §4), which hit it writing `le_iff_exists_add` and took the call spelling.
