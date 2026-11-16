---
title: Result eliminators are called with all three type arguments spelled out; find out whether they have to be
status: closed
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
  (`docs/elaborator/complete-post-attribution-design.md` §10.7).
- 2026-09-16: Answered: **(2), they were not required.** The showcase now calls the
eliminators as the `self` methods they are declared as, with nothing annotated:
`first.and_then(λ left => recognize_certified(plus,0,source,left.end).fold(λ op => …, λ ignored => …))`.
Three things came off, each probed separately and each checking clean: the
eliminators' type arguments (8 calls), their continuations' parameter types
(16 lambdas), and `recognize_certified`'s `<PTok,Nat>`/`<PTok,Expr>` (5 calls).
The dependent positions — types indexed by `begin`, a variable of the enclosing
telescope — were never the obstacle they looked like, and the capability was
already pinned by `crates/elab/tests/callback_expected_types.rs`; the showcase
simply was not using it.

Cost, serial, two reps on the furnace: **counts improve, seconds do not move.**
Conversion misses 46 497 -> 45 920, evaluator steps 1 142 770 -> 1 129 562,
unify calls 1 522 -> 1 463, queries +3 833 (+0.07 %); wall 51.4/50.7 s against
51.2/51.4 s and item totals within each spelling's own repeat spread. Per item
the misses halve where the annotations were densest (`expr_body` 383 -> 186,
`factor_body` 399 -> 202, `parentheses_body` 27 -> 9). So the annotations were
costing a little conversion and buying nothing — but this is a readability
result, not a performance one, and should not be quoted as a speedup.

No residue: no other file in `lib/` or `docs/showcase/` writes the pattern. The
two occurrences in `crates/elab/tests` are deliberate tests of the qualified
spelling and stay. Closing.
