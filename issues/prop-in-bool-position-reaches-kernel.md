---
title: A proposition in a Bool position is refused by the kernel as LevelMismatch
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-10-07
updated: 2026-10-07
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
