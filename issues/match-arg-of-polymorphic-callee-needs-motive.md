---
title: "A match passed to a polymorphic function is elaborated in inference position, so it demands a motive"
status: open
labels: [frontend,elaboration,inference,ergonomics]
created: 2026-08-17
updated: 2026-08-17
---

Found writing `std/list`'s `len_filter` ([[std-list-api]], 2026-08-17). A
`match` handed to a **polymorphic** callee is refused:

```heather
theorem a1<A>(b: Bool, xs: List<A>): len(match b { True => xs, False => Nil }) = 0 { ?p }
// error: `match` in inference position needs a motive: `match e as λ z => T { … }`
```

while the same shape at a **monomorphic** callee is fine:

```heather
fn twice(n: Nat) -> Nat { add(n, n) }
theorem a2(b: Bool): twice(match b { True => 1, False => 2 }) = twice(…) { refl }   // ok
```

Both workarounds confirm the diagnosis, and either one alone is enough:

```heather
len(match b as λ c => List<A> { True => xs, False => Nil })   // annotate the match
len<A>(match b { True => xs, False => Nil })                  // or spell the type argument
```

So the rule biting here is not about `match` at all. `len`'s parameter type is
`List<A>` with `A` unsolved, so the argument has no expected type yet and is
elaborated in *inference* position; `match` in inference position needs a
motive, correctly, because in general its branch types differ. The two facts
are each right and the composition is not: the writer sees a `match` whose arms
are visibly one type, in an argument position whose type they consider obvious.

## Why it is worth fixing rather than annotating

The annotation is not merely verbose, it is **redundant with the callee**: the
motive states the very type the callee's parameter already gives, so the reader
of `len_filter` in `lib/std/list.hthr` meets a five-line motive whose whole
content is `List<A>`. And the trigger is common in exactly the position the
library is now in — every list function is polymorphic, and case analysis on a
`Bool` or a `Decide` inside one is the ordinary way to write a program.

## Two routes

1. **Postpone the argument.** Elaborate the other arguments first, solve the
   type parameter from them, then check the `match` against the now-known
   type. `len`'s only argument is the `match`, so this fixes nothing here.
2. **Give a non-dependent `match` an inferable motive**: elaborate the arms,
   take their common type if they agree up to conversion, and fail as today if
   they do not. Fixes the case above and the whole class, and stays
   conservative — a dependent motive still has to be written, because arms
   that disagree still cannot be joined.

Route 2 is the one this issue asks for; route 1 is a general elaborator
improvement ([[elab-unifier-completeness]] territory) that would help other
shapes and not this one.

## What it assumes from elsewhere

- **[[elab-unifier-completeness]]** owns postponement. Assumed here: only
  that argument elaboration is left-to-right and not postponed today.
- **[[exists-type-arg-not-inferred]]** (closed) owns argument-directed type
  inference. Assumed here: only that a type parameter is solved from the
  arguments' types, which is why an unsolved one leaves no expected type.

## Acceptance

`len(match b { True => xs, False => Nil })` checks with no motive and no
spelled type argument, and `lib/std/list.hthr`'s `len_filter` loses its inner
`as λ c => List<A>`. A negative control stays: a `match` whose arms have
genuinely different types still asks for a motive, with today's message.
