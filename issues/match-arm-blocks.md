---
title: A match arm is an expression, so `let` cannot be used inside one
status: open
labels: [frontend,syntax,elaboration,ergonomics]
created: 2026-08-02
updated: 2026-08-02
---

Noticed while writing the tabulate suite's checking-position fixture (the
quotation-stage port round, 2026-08-02): an arm's right-hand side is parsed
with `expr()`, not as a block, so `Succ(k) => { let y = f(x); g(y) }` has no
spelling — any arm that wants a local binding must inline it or hoist it to a
helper `fn`. The tabulate suite used argument position instead.

Related but distinct from [[annotated-let-swallows-the-equals]] (that one is
about the annotation's `=`; this one is about arms not admitting statements
at all). Together they make `let` unusually weak: not writable annotated, not
writable in arms.

Wanted: either arms accept a block expression, or a general
`{ stmt*; expr }` block-expression form both sites share. The latter likely
subsumes [[nested-goal-discharge]]'s wish for a hole inside an `on`
right-hand side — check when designing.
