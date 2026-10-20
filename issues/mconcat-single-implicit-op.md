---
title: Let proof lemmas take their operation implicitly: mconcat_single(x)
status: open
labels: [design,frontend,ergonomics,traits]
area: language
created: 2026-08-11
updated: 2026-08-11
---

`mconcat_single<A: Monoid(op)>(op: A -> A -> A, x: A): mconcat(op, Cons(x, Nil)) = x`
makes its callers name the operation (`mconcat_single(append, xs)`,
`mconcat_single(and, b)`). User observation (2026-08-11): it is a *proof* — at
any use site the caller is proving something about a `mconcat(op, …)` they
already wrote, so the operation is sitting in the goal and unification would
find it. `{op: A -> A -> A}` implicit would make the calls `mconcat_single(x)`.

The question is not mechanism (implicit value parameters exist) but policy:
which of a lemma's parameters deserve to be implicit. The lean the observation
suggests: a **computational** function keeps its operation explicit — `mconcat`
callers choose the structure, nothing is in a goal to infer from — while a
**lemma about it** may take the same parameter implicitly, because its checking
position (the stated equation) determines it. That split would also apply to
future append/fold laws before the library grows more of them.

Worth deciding before the algebra lemma population grows; retrofitting
implicitness later touches every caller.

## What it assumes from elsewhere

- **[[traits]]** owns constraint slots and instance search. Assumed here: only
  that the linked slot `Monoid(op)` works unchanged when `op` is implicit.

## Log

- 2026-08-11: bare-symbol-checking-carrier landed 2026-08-11; the policy-split lean (computational explicit, lemmas may infer) reads the same but the computational side's explicitness is now often a symbol rather than a positional name. Not decided here.
