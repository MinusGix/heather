---
title: Projection sections: ·.field for λ s => s.field
status: open
labels: [frontend,surface-syntax,ergonomics]
created: 2026-10-07
updated: 2026-10-07
---

Programs pass record projections as functions, written as lambdas
(`wc.hthr:76-89`):

```heather
[Column('l', λ s => s.lines, wc_lines), Column('w', λ s => s.words, wc_words), …]
fold_counts_runs(wc_step, λ s => s.words, λ s => s.inside, space, …)
```

Argument-slot sections exist (`·`, [[argument-slot-sections]],
`docs/argument-slot-sections-design.md`) and cover `f(·)`. Wanted: a
projection section, so `λ s => s.lines` is `·.lines` (or another spelling
such as `.lines` at a function-typed checking position).

It does not today. Probed 2026-10-07, at a position whose expected type is
`S → Nat`:

```text
fn k() → S → Nat { ·.a }
error: no field `a` here (and the receiver's type could not be inferred)
```

The slot's binder type is known from the expected Pi, so the receiver could
be inferred from it. The question left is whether `·.a` is the spelling, or
whether a shorter one (`.a` at a function-typed checking position) is also
wanted. A projection section
also gives [[command-bundle-ergonomics]] a syntactic field reference to
read, which today's producer recovers by evaluation.

## What it assumes from elsewhere

- **[[argument-slot-sections]]** owns `·` and its checking-position rules.
  Assumed here: only that a projection is a candidate slot context.
