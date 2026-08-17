---
title: "A match passed to a polymorphic function is elaborated in inference position, so it demands a motive"
status: closed
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

## What landed (2026-08-17)

Route 2, as `Elaborator::infer_match_constant_motive`: a motive-less `match` in
inference position takes its motive from an arm that **binds nothing** —
whose body is therefore scoped in `Γ` and needs no branch context — and every
other arm, binding or not, is then *checked* against that type by the ordinary
path. So the reading is widened and the meaning is not: nothing here joins arm
types, and a dependent `match` still has to say so.

Three properties keep it honest:

- **Any** non-binding arm, not the first: one whose body does not infer either
  (`Nil` on its own) is stepped over rather than fatal.
- **Speculation does not nest** (`Elaborator::motive_speculation`). A nested
  motive-less `match` declines instead of speculating, so the work at depth
  `d` is linear rather than `2^d` — the shape
  [[type-argument-speculation-cost]] was filed for, and the reason this is a
  flag rather than a syntactic scan of the arm.
- **A failed attempt leaves no trace**: warnings and any minted goal are rolled
  back. The goals are not bookkeeping — a hole is registered by span, and the
  attempt elaborates the arm in `Γ` while the real pass elaborates it inside
  the branch context, so a surviving registration would meet `new_goal`'s
  "re-elaborated in a different context" refusal and turn a decline into an
  internal error.

Tests: `crates/elab/tests/motive_synth.rs` — the headline, one-arm-binds-
nothing-is-enough, every-arm-binds still asks for the motive, and the
stage-2 *checking*-position synthesis undisturbed. Library:
`lib/std/list.hthr`'s `len_filter` lost its inner `as λ c => List<A>`; the
outer motive stays, because that one is doing real dependent work.

**What it bought beyond its own acceptance**, found by the four suite probes
that had to change: an unannotated `let x = match r { … };` elaborates now.
That position is inference for the same reason the argument was — nothing
supplies an expected type — and it is a spelling a writer reaches for
constantly.

Those probes are also a finding about the *tests*. In
`match_equation_split.rs` and `records.rs` the refused motive-less `match` was
being used as a **stand-in for "an expression whose type is unknown"** — the
`records.rs` one wants a receiver nobody could have read, and reached for a
`match` to get one. Three probes were rewritten onto an every-arm-binds
`match`, which is the honest way to ask for that; where the test's subject was
the motive message itself, that is now also the only shape that produces it.

## Two pieces of residue, with owners

1. **A binding arm still cannot name the type.** Reading one means
   reconstructing that arm's context, which is per-lowering work (`elab_arm`'s
   Σ-walk, the case tree, the `Wf` eliminator) and has no customer: every case
   the library has met has a non-binding arm. Recorded as a decision that owes
   nothing rather than filed — if a customer appears, it is a new issue with a
   real example in it.
2. **Arms that disagree now report as a kernel rejection** rather than as
   "needs a motive", because checking discards the expected type and the
   kernel is what notices. That is [[check-fallback-discards-expected-type]],
   filed by this round, and it is *pre-existing*: the same arms with the motive
   written report the same way, which is the invariant this change was built
   to preserve.

## Acceptance

`len(match b { True => xs, False => Nil })` checks with no motive and no
spelled type argument, and `lib/std/list.hthr`'s `len_filter` loses its inner
`as λ c => List<A>`. Met, with the negative control **as landed rather than as
written here**: the control that survives is *every arm binds* (no arm can
name the type, so the motive is still asked for). Arms that merely disagree do
not come back to this message — they are checked against the named type and
refused where any wrong arm is refused, which is the kernel; §Residue 2 records
that and who owns it. The as-written control was a guess about a mechanism that
turned out not to be the one, and it is left visible rather than rewritten.
