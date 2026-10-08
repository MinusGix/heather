---
title: A proposition in a Bool position is refused by the kernel as LevelMismatch
status: closed
labels: [frontend,elaboration,diagnostics]
created: 2026-10-07
updated: 2026-10-08
---

A proposition written where a `Bool` is expected is not refused by the
elaborator; the kernel refuses it with a message that names neither type.
Probed 2026-10-07 at `b5b2b9d`:

```text
import nat;
import bool;
fn z(n: Nat) → Bool { n = 0 }

error: the kernel rejected `z`: LevelMismatch
```

The same happens with `fn nl(b: BitVec(8)) → Bool { b = '\n' }`. This is the
first thing an author tries when writing a byte predicate, and the error
does not say that `n = 0` is a proposition or point at `decide_bit`.

Wanted: the elaborator refuses a Prop-valued expression checked against
`Bool` with a diagnostic naming both, and suggests `decide_bit<…>()` when a
`Decide` instance resolves. Whether that position should instead elaborate
to `decide_bit` is [[bool-from-decidable-prop]]'s question.

## What it assumes from elsewhere

- **[[bool-from-decidable-prop]]** owns whether the form becomes legal.
  Assumed here: only that, until it does, it should be an elaborator error.

## Log

- 2026-10-08: FIXED. The checking fallback (`elab_check_skel`'s `_` arm) now refuses an
  expression whose inferred type is a universe when the expected type is not
  one, at the expression, through `Elaborator::type_where_value_expected`.
  The kernel's verdict on this shape is `LevelMismatch`, and `kernel_error`
  reads the deferred check notes only for `NotConvertible`, which is why the
  note mechanism never spoke here.

  The refusal is made only on a decided answer: the semantic conversion of the
  inferred universe against the expected type must say `NotConvertible`, so a
  universe reached through a δ-step the caller's reduction does not take
  (`fn Props() -> Type<1> { Type }`, `fn q(n: Nat) -> Props() { n = 0 }`)
  is still accepted. It runs only when the inferred type is a universe that
  differs syntactically from the expected one, which no well-typed site does.

  Messages, at the expression:

  - expected converts to `bool::Bool` and a trial `bool::decide_bit<P>()`
    resolves: "this is a proposition, but a `Bool` is expected here;
    `decide_bit<…>()` around it reads its decision as a `Bool`";
  - expected is `Bool` and no `Decide` instance resolves: "… and it has no
    `Decide` instance to read its decision as one";
  - any other non-universe: "this is a type (it has type `Type<0>`), but a value
    of `Two` is expected here".

  The trial runs under `MatchRollback`, like any declined speculation. Tests:
  `crates/elab/tests/decidable_if.rs` (both issue shapes' Nat form, the
  no-instance form, a non-Bool target, and the universe-through-a-`fn` and
  `decide_bit` controls). Probed by hand: `fn nl(b: BitVec(8)) → Bool { b = '\n' }`
  under `tr_s.hthr`'s imports gets the `decide_bit` hint.
