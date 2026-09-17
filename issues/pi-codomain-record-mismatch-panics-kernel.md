---
title: A Pi codomain mentioning its binder panics the kernel when the body mismatches
status: open
labels: [kernel,elab,bug]
created: 2026-09-17
updated: 2026-09-17
---

Checking a body against a **Π whose codomain is a type application mentioning
the binder** aborts the process with a kernel invariant violation as soon as
the body does *not* have that type. The mismatch report never gets written.

```heather
import logic;
theorem t<A>(P: A → Type, R: Type, h: R): (a: A) → And<P(a), R> { h }
```

```text
thread 'main' panicked at crates/kernel/src/subst.rs:1150:9:
kernel invariant violated: local variable 5 escapes the substitution's target
entries (variables cannot address a context-variable base)
```

It is a **panic, not a diagnostic**: `heather check` dies, so nothing else in
the file is reported.

## What was measured (2026-09-17)

Run on both the parent commit and the [[iff-in-type-valued-body]] tree; they
behave identically, so this is not that round's doing.

- Panics: `(a: A) → And<P(a), R>` expected, `h: R` supplied.
- Panics the same way with the notation: `(a: A) → (P(a) ∧ R)`.
- **Checks** when the body does have the type:
  `h: (a: A) → And<P(a), R>` against the same expected type — so the Π itself
  is fine and it is the *refusal* path that breaks.
- **Reports cleanly** when the codomain is a bare application rather than a
  type application: `(a: A) → P(a)` expected, `h: R` supplied, gives
  ``this has type `R`, but `(x: A) -> P(x)` is expected here``.
- **Reports cleanly** when the offending type is the *hypothesis* rather than
  the expected type: `h: And<(a: A) → P(a), R>` against `R`.

So the discriminator is: the **expected** type is a Π, its codomain is a
`TyKind::Named` whose arguments mention the binder, and the check fails.

## Why it matters beyond the crash

A kernel `assert`-class invariant reachable from ordinary surface source is a
crash, not a refusal — the term handed to `subst` is malformed, and the
question of *who* built it (the
mismatch renderer, or the checking path that precedes it) is the first thing to
answer, because a malformed term that merely happened to be on its way to an
error message is a different severity from one the checker itself builds.

## Acceptance

- The reproducer above reports an ordinary type mismatch and exits non-zero.
- The invariant is not merely silenced: name which builder produced the term
  whose variable escaped, and fix it there.
- A regression test with an **open** carrier (`A` a type parameter) and a
  codomain that genuinely depends on the binder, since a closed codomain does
  not reproduce it (docs/testing-generated-terms.md).

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `And`; it is incidental here — any declared
  type constructor applied to the binder should do, and that is worth checking
  when the fix is scoped.

## Log

- 2026-09-17: Filed from the [[iff-in-type-valued-body]] round, which hit it
  probing adjacent connective spellings. Confirmed pre-existing by rebuilding
  the parent commit.
