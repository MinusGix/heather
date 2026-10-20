---
title: An if in a module without import bool reports decide_bit's type arguments
status: open
labels: [diagnostics,elaboration]
area: language
created: 2026-10-02
updated: 2026-10-02
---

Since [[native-frontend-decided-matches]], `Decide` lives in `bool` and an
`if P` without evidence lowers to `match decide_bit<P>()`. In a module that
imports `logic` but not `bool` (enough before the move), the `if` fails with
"`decide_bit` takes no type arguments (only a `fn` or `theorem` declared
`decide_bit<A, …>` does)". That names a parser-generated call the writer
never wrote. It should say what `decide`'s goal combinator already says: the
`if` needs the class in scope, so `import bool;`.

Where: `if_resolution_error` (crates/elab/src/matching.rs) rewrites only
resolution failures. An unbound or non-generic `decide`/`decide_bit` head at
`MatchForm::If` should get the import message too. The old failure for a
missing `logic` was just as indirect, so this predates the move.
