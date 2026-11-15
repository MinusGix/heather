---
title: A written motive that names the scrutinee meets the convoyed window as a bare NotConvertible
status: open
labels: [frontend,elaboration,diagnostics,design]
area: language
created: 2026-08-17
updated: 2026-09-18
---

Filed off [[recursion-at-deeper-subterms]] (closed 2026-08-17,
docs/language/recursion/course-of-values-recursion-design.md §5), which records the reasoning this
issue exists to test.

A course-of-values recursion convoys its window of past values through the
nested `match` on the chain. In the `Succ(l)` arm the window's *head* — the
value the enclosing arm knew as `k` — arrives at type `M[Succ l]`, not `M[k]`.
So a self-call at `k` inside that arm lowers to a term about `Succ l`.

**That is consistent when the motive is synthesized**, and the design doc says
so: clear-and-generalize abstracts every occurrence of `k` from the arm's
expected type, so the goal was refined to `Succ l` too and the two agree.

The argument does not cover a motive the writer **wrote**:

```
match k as λ y => …k… { Zero => …, Succ(l) => … half(k) … }
```

An `as`-motive is used as written, so it may mention `k` freely while the
convoyed component speaks of `Succ l`. Nothing unsound follows — the kernel
refuses — but what the writer gets is `NotConvertible` with no span inside the
arm and no hint that the *motive's* spelling is what did it, which is the worst
diagnostic in the language for the amount of thinking it costs to unpick.

## What is actually unknown

Whether the case is reachable at all. Two things have to line up: a written
motive that names the scrutinee, inside a `match` that is on a course-of-values
chain. Nothing in `lib/` does this today — the parity section's nested matches
are all motive-less — and it may be that any motive naming `k` there is already
wrong for an independent reason.

So the first move is a **probe, not a fix**: write the shape, see which of
(checks / refuses cleanly / refuses obscurely) actually happens, and only then
decide between a diagnostic, a refusal at the motive, and doing nothing.

## Options, if it is reachable

1. **Refuse at the motive**, naming the scrutinee occurrence and saying the
   arm's window speaks of `Succ l` — the cheapest honest answer.
2. **Substitute the refinement into the written motive** where the arm's
   constructor determines it, which is what the synthesized path effectively
   does. Bigger, and it changes what an `as`-motive means.
3. **Nothing but a note**, if the shape turns out unreachable or already
   refused earlier with a good message.

## What it assumes from elsewhere

- **[[recursion-at-deeper-subterms]]** (closed) owns the convoy. Assumed here:
  only that the window's head is anchored at the chain's head, which is §5.1 of
  its design doc.

## Log

- 2026-09-18: Probed while closing [[utf8-encode-decode-strictness]]. The shape is
  reachable and refuses cleanly, with the wrong message. A `fn` with a written
  CONSTANT motive on the chain `match` (`match r as λ rr => Nat { … skip2a(r2) … }`)
  checks, so a written motive as such does not drop the window. A theorem with a
  written dependent motive that names the scrutinee
  (`match r as λ rr => skip2(Cons(a, rr)) = n → n <= list_len(Cons(a, rr)) { … skip2_le(r2, …) … }`)
  is refused as "must descend … this one is not [chain-shaped]" — the `cov: None`
  text — and so is the SAME goal with the motive synthesized, so the case is
  owned by [[cov-window-in-theorem-arms]] (a hypothesis mentioning the
  scrutinee), not by the written motive. What this issue owns is the message:
  "not chain-shaped" about a `List` is option 1's diagnostic gap made concrete.
