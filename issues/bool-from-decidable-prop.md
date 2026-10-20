---
title: Write a decidable proposition where a Bool is expected
status: open
labels: [frontend,elaboration,surface-syntax,design]
area: language
created: 2026-10-07
updated: 2026-10-08
---

A Bool-valued predicate on a decidable proposition is written through
`decide_bit` (`wc.hthr:32`):

```heather
fn newline(b: BitVec(8)) → Bool { decide_bit<b = '\n'>() }
```

`if b = '\n'` already reads the decision without the wrapper
([[native-frontend-decided-matches]]: `if P` lowers to
`match decide_bit<P>()`). The same move in a Bool-expected position would let
the body be `b = '\n'`: when a proposition `P` is checked against `Bool` and
`Decide<P>` resolves, elaborate it as `decide_bit<P>()`.

Today the bare form is not refused by the elaborator: probed 2026-10-07,
`fn z(n: Nat) → Bool { n = 0 }` reaches the kernel and fails as
"the kernel rejected `z`: LevelMismatch"
([[prop-in-bool-position-reaches-kernel]]). Whatever this issue decides,
that position needs a real diagnostic.

Questions:

- **Is it too implicit?** Heather keeps Prop and Bool apart on purpose
  (`==` is not syntax; `<` is Prop-valued). A coercion only at a checking
  position whose expected type is literally `Bool`, and only when an instance
  resolves, is narrow. A failure should name the missing `Decide` instance,
  not report a Prop/Bool mismatch.
- **Or an explicit, shorter spelling** (`decide(b = '\n')`, `⌜b = '\n'⌝`),
  if a silent coercion is unwanted.
- **Proofs.** Specs that use the Bool (`filter(newline)`) and proofs that
  split on it must see the same term as today, so the elaborated form should
  be exactly `decide_bit<P>()`, not a new head.

## What it assumes from elsewhere

- **[[native-frontend-decided-matches]]** owns how `decide_bit` is read by
  the elaborator and the structured frontend. Assumed here: only that a
  resolved `decide_bit<P>()` is what both read.

## Log

- 2026-10-08: Its interim error landed: a proposition in a Bool position is now an elaborator refusal at the expression that names `decide_bit<…>()` when `Decide` resolves ([[prop-in-bool-position-reaches-kernel]]). The coercion question here is unchanged.
