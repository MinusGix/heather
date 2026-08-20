---
title: An ambiguous constructor name in a deep pattern is silently read as a binder
status: closed
labels: [frontend, elaboration, patterns, modules]
created: 2026-08-16
updated: 2026-08-20
---

Found in passing while landing [[ctor-resolution-by-expected-type]] (2026-08-16),
verified with a throwaway test, and **not fixed** there: that round's judgment is
expression checking position, and this one needs evidence the pattern compiler
does not have yet at the point it decides.

The pattern compiler must decide whether a bare identifier in a sub-pattern is a
nullary constructor or a fresh binder — the parser cannot
(`docs/nested-match-patterns-design.md` §3.5). It decides with
`patterns.rs:is_ctor_name`, which consults the **global** constructor table with
no type evidence at all. So an ambiguous name answers `false`, and a
constructor becomes a binder:

```heather
// module a: inductive Res<A> { Stuck, Out(v: A) }
// module b: inductive Alt { Stuck }
import a; import b;
fn f(r: Res<Res<Nat>>) -> Nat {
    match r { Stuck => 0, Out(Stuck) => 1, Out(Out(v)) => v }
}
```

`Out(Stuck)` binds a variable named `Stuck` that matches everything, so `f`
returns 1 on every `Out`, the third arm is dead, and nothing says so. The
observable failure is a kernel rejection at the first theorem that computes
through it (`the kernel rejected `t`: NotConvertible`) — a message about a term
nobody wrote, several steps downstream of the misreading.

## Why this is the bad kind of wrong

It is a **silent reinterpretation**, which is the one thing
`docs/modules-design.md` §8's second invariant exists to forbid: adding a second
visible `Stuck` does not make the file an error, it makes it mean something
else. Every other member of the resolution family is honest about this — the
outer arm name goes through `arm_ctor_index` (the scrutinee's type, so
visibility never enters), and expression checking position now goes through the
expected type, with an explicit "if any visible candidate is not a constructor,
stand down" guard so it can only ever shrink a candidate set.

The same defect is *not* reachable at the outer arm, and not reachable at a
nullary name in expression position — only inside a deep pattern's column.

## What a fix has available, and what it does not

The sibling of [[inner-column-diagnostic-span]], and for one shared reason: an
inner **column** has less information than the arm around it, at the moment the
pass needs it.

`reclassify` runs at the very top of `prepare_arms`
(`crates/elab/src/patterns.rs:144`), deliberately — the comment says "done
before anything else, so `is_deep` below sees the reclassified shape", and
`matrix`, which is what would know a column's type, runs after it and reads the
already-reclassified patterns. So the scrutinee type is in hand (`scrut_ty`) but
a *column's* type is not, and the ordering is load-bearing rather than
incidental. Two shapes to weigh:

- classify per column during the matrix walk, so each sub-pattern is decided
  against the field type it actually sits at — the honest answer, and a
  reordering of the pass rather than a new lookup;
- keep the pre-pass and give it the constructor names reachable from
  `scrut_ty`'s declaration transitively — cheaper, and wrong at the first
  column whose type is not one of those.

Deliberately **not** "make `is_ctor_name` fall back to something": there is no
type evidence at that call site to fall back *to*, and guessing is how this
became silent in the first place.

## When

Triggered, weakly: it needs two visible declarations sharing a constructor name
*and* a deep pattern, which no file in `lib/` has today. The trigger to watch
for is the standard library growing a second `Nil`/`None`/`Ok`, at which point
this stops being hypothetical and starts being a wrong answer.

## What it assumes from elsewhere

- **[[nested-match-patterns]]** owns the pattern compiler and §3.5's
  classification rule. Assumed here: only that the classification stays the
  compiler's to make — a parser that could tell them apart would delete this
  issue instead of fixing it.
- **[[modules]]** owns the name regime. Assumed here: only §8's second
  invariant, that library growth may introduce errors and never
  reinterpretations.

## Log

- 2026-08-20: Closed. The pattern prepass now carries the actual lowered type
  of each constructor-field column and classifies a bare identifier only
  against that type's constructors. Payload types come from the instantiated
  Sigma spine (`Outer<A>` at `Outer<Inner>` therefore exposes `Inner`), plain
  recursive children carry the scrutinee type, and primitive Nat/Fin retain
  their constructor rules. The generated decision tree and all lowerers are
  unchanged. The module regression crosses two colliding Option constructors,
  a colliding recursive child, and the negative control where the same name at
  Nat remains a binder. Full `scripts/test`: 1978 passed, 0 failed.
