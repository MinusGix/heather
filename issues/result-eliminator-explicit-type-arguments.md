---
title: Result eliminators are called with all three type arguments spelled out; find out whether they have to be
status: open
labels: [frontend,elaboration,inference,stdlib,ergonomics]
created: 2026-09-16
updated: 2026-09-16
---

Every `Result` eliminator call in `docs/showcase/calc_parser.hthr` spells all
three type arguments in full:

```heather
result::and_then<Certified<PTok,Expr>(source,begin,GrammarSpec(1)),
        Certified<PTok,Expr>(source,begin,GrammarSpec(0)),Failure<PTok>(source)>(first,
    λ (left: Certified<PTok,Expr>(source,begin,GrammarSpec(1))) => …)
```

There are eight such calls (`and_then` x3, `fold` x5, `map_err` x1), and after
the 2026-09-16 cleanup they are the largest remaining source of noise in the
file — the scrutinee `first` determines the first and third arguments, and the
continuation's result determines the second.

**The question this issue exists to answer is which of two things is true**,
because they want opposite responses and the file cannot distinguish them:

1. The annotations are **required** — the elaborator cannot infer them for a
   value whose type is indexed by `begin`, a bound variable of the enclosing
   signature. Then this is an inference gap on exactly the shape the checked
   parser library pushes every client into, and it belongs next to the other
   inference issues.
2. The annotations are **not required** and were written defensively. Then the
   showcase is teaching a habit nobody needs, and the fix is to delete them —
   after checking what they cost, since an explicit type argument is also a
   term the kernel does not have to reconstruct.

Settling it is one probe: delete the type arguments from one `fold` call and
run `heather check` on the showcase. Note `-L docs/showcase -L lib/std/parser`
is refused (both declare `parser_core`); copy `calc.hthr` and `calc_parser.hthr`
to a scratch directory and point `-L` there.

If (1): the shape is `f<A,B,E>(r: Result<A,E>, k: A -> Result<B,E>)` where `A`
and `E` come from `r`'s inferred type and `B` from the continuation's, with all
three mentioning a `Cursor<T>(source)` bound by the caller's telescope. That is
a plain first-order inversion, not higher-order unification, so if it fails it
is worth knowing why before adding another special case.

## What it assumes from elsewhere

- **[[elab-unifier-completeness]]** owns what the unifier can solve. Assumed
  here: only that "infer a function's type arguments from the type of a given
  value argument" is within its charter rather than a separate mechanism.

## Log

- 2026-09-16: Noticed during the `calc_parser.hthr` readability pass. Not
  probed — the file was left with the annotations it had, since removing them
  changes elaborated terms and that file is a quoted perf fixture
  (`docs/complete-post-attribution-design.md` §10.7).
