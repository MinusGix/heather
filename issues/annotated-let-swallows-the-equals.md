---
title: An annotated `let` at a non-equality type does not parse
status: open
labels: [frontend,syntax,parser]
created: 2026-07-26
updated: 2026-07-26
---

```heather
fn f() -> Nat { let n: Nat = 3; n }
```

```
parse error: expected `=`, found Semi
```

**Pre-existing**, confirmed by running the same input against the parser as of
`13dd25d` (before [[surface-function-types]]); it is not a regression from
that round, which is only how it was found.

## Why

`let_stmt` parses the annotation with `ty()`, and `ty()`'s equality case takes
the first `=` it sees:

```
let  n  :  Nat  =  3  ;
            └─ ty() ─┘        annotation parsed as the type `Nat = 3`
                        ^ let_stmt now wants `=`, finds `;`
```

This is deliberate for the *other* reading and is tested
(`parser::tests::let_binds_with_and_without_an_annotation`,
`let p: a = b = pf;`), which the comment on `let_stmt` spells out: "`=` is not
an expression operator, so `ty()` stops after `a = b`". What nobody wrote down
is that the same greed makes a **non**-equality annotation unparseable, because
there is then no second `=` for the statement.

So `let` is currently usable either *unannotated* (`let n = 3;`, which infers
and is what every test in the suite does) or annotated at an equality type
(`let p: a = b = pf;`). The middle case — annotated at any other type — is the
hole, and it is exactly the spelling [[goal-holes]] recommends in its own
diagnostic ("annotate it (`let p: T = ?;`)").

## Why it is not a one-line fix

`let x: T = e;` and `let p: (a = b) = pf;` are genuinely ambiguous under a
greedy `ty()`. Resolving it is a grammar decision, not a typo fix:

- **Scan for the last top-level `=`** before the `;` and treat that as the
  binder's `=`, everything before it as the annotation. Handles both, and is a
  single lookahead pass in the style of `parser.rs::group_is_type`. Fails on a
  `let` whose *value* contains a top-level `=`, which today nothing can.
- **Require parentheses** on an equality annotation (`let p: (a = b) = pf;`).
  Simplest rule, breaks the existing spelling and its test.
- **A different binder token** for `let`, e.g. `:=` (already lexed, and used
  by `on` discharge). Clean separation, and it is the one that composes with
  [[effects-direction]]'s eventual assignment `=`. Breaks the existing
  spelling too.

The first is the least disruptive; the third is arguably the most principled
given [[surface-syntax]]'s settled story that `=` is binding *and* equality.

## Log

- 2026-07-26: Found while probing hole-under-lambda behaviour for
  [[surface-function-types]]; confirmed pre-existing rather than a regression
  by re-running the input against the previous commit's parser. Not fixed in
  that round because choosing between the three options above is a grammar
  decision that should not ride along inside a function-types commit.
