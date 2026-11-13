---
title: A constructor in a deep pattern is silently a binder where the column's type is not yet known
status: closed
labels: [frontend,elaboration,patterns]
area: language
created: 2026-11-12
updated: 2026-11-12
---

Found 2026-11-12 on PR #551 while writing the `laid` generator
(`lib/std/machine/laid.hthr`): a list of two constructors took the arm
for a list of one. A sibling of [[deep-pattern-ctor-needs-column-type]],
which made the pattern compiler classify a bare identifier in a
sub-pattern against its column's type and not the global constructor
table. Where the column's type is **not known** when the pass runs, the
identifier is still read as a binder, silently.

```heather
import tactic;

fn bound(t: Tac<List<Nat>>) → Tac<Bool> {
    let xs <- t;
    match xs {
        Cons(c, Nil) => pure(True),
        _ => pure(False),
    }
}

// Accepted today: `Nil` is a variable that matches every tail.
theorem bound_true(): bound(pure([1, 2])) = pure(True) { refl }
```

The same match in a function of its own, under a written
`t.bind(λ xs => …)`, or under a plain λ answers `pure(False)`. What
differs is that `let xs <- t;` lowers to `Bind::seq(t, λ #bind => …)`
(`crates/syntax/src/try_lower.rs`), whose continuation is elaborated
before the carrier's instance has said what `xs` is. The match finds
`List` from `Cons`, but `Elaborator::pattern_fields_at`
(`crates/elab/src/patterns.rs`) answers `None` for the fields' columns
at that type, so `reclassify_at` leaves `Nil` a `Pat::Var`.

No warning is printed: `Nil` is used nowhere and is not reported as an
unused payload either.

## Why it matters

It is the silent reinterpretation that issue called the bad kind of
wrong, and it is in the spelling tactic and generator code uses most: a
`let x <- request;` followed by a match on the answer. Every nested
nullary constructor there (`Cons(a, Nil)`, `Some(Nil)`, `Accepted(None)`)
is at risk, and the library's tactics may already hold some.

## What a fix has

- **Refuse what cannot be classified.** Where a column's type is not
  known and a bare identifier in it is a visible constructor's name, say
  so: the pattern would bind a variable named like a constructor, the
  scrutinee's type is not known here, annotate it (`let xs: List<Nat> <- t;`)
  or match the field in the arm. An error and not a guess, for the
  reason the sibling gives.
- **Know more columns.** A constructor's plain recursive field has the
  scrutinee's own type whatever its parameters are, so `Cons(c, Nil)`'s
  second column needs no payload spine; and a payload whose type has an
  unsolved parameter still has a head.
- Either way the pass could run after the continuation's parameter is
  solved, which is the bind lowering's order and a larger change.

## Acceptance

- The program above answers `pure(False)`, or is refused with a message
  that names `Nil` and the unknown type; never `pure(True)`.
- A probe in `lib/_tests` for each: a plain recursive field, a payload
  field (`Some(Nil)`), and a negative control where the name is no
  constructor in scope and stays a binder.
- The whole library re-elaborated: every match whose reading changes is
  a bug found, listed in the log.

## Log

- 2026-11-12: Fixed 2026-11-12 on PR #551 (`crates/elab/src/patterns.rs`). The cause was narrower than "not yet known": the scrutinee's type was known but arrived unreduced, `El(app(M, A))` for the variable of a bind, and `Elaborator::pattern_fields_at` read the constructors' spine from the type as written, which has none. It now reads the reduced type where the written one has no spine. A type a function computes (`Maybe(List<Nat>)`) had the same fault and is fixed with it; a type named by a `def` was already read rightly.

  The refusal is in as well (`check_classifiable`): a visible nullary constructor's name in a column whose type cannot be read is an error that names the constructor. No source spelling was found that reaches it after the fix (an unannotated λ is refused before its match is read), so it guards the reader and has no probe.

  Probes: `lib/_tests/lang/deep_pattern_reduced_type_tests.hthr` (a plain recursive field, a payload field, two levels, the same at `Option`'s bind, the binder control, and the old reading as a `¬`-style refusal). The laid generator's matches (`lib/std/machine/laid.hthr`) stay written a level at a time.

  Whole library re-elaborated with the fixed compiler: see the round's verification; a module whose reading changed would be listed here.
- 2026-11-12: Verified 2026-11-12 (PR #551): every library module (516) was elaborated again by the fixed compiler with no stale images and all check, so no library match changed its reading in a way a theorem observes and none meets the refusal; `scripts/test --pr` is `== suite: 4019 passed, 0 failed, 3 ignored ==`. Acceptance is met but for a probe of the refusal, which no source spelling reaches.
