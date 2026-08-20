---
title: A lowered inductive instance cannot say what type arguments it was instantiated at
status: closed
labels: [frontend,diagnostics]
created: 2026-08-17
updated: 2026-08-20
---

Residue of [[le-diagnostics-print-raw-el]] (2026-08-17). The surface speller
prints an inductive instance as its declaration's name, recovered from the
nominal tag in the lowering's leftmost constructor — so a context binder that
used to be ~250 characters of `Wf[0](Σ…)` is now `List<…>`. The ellipsis is
literal, and it is an admission: **the type arguments are not recovered**, so a
`List<Nat>` and a `List<Bool>` in the same message print identically.

The cause is that the lowering *monomorphizes*. `lower_ctor` substitutes each
type argument into the constructor field types and nothing records that it did;
`Inductive::params` holds parameter *names* only, and the `datarepr`/monomorph
registries key on a surface argument spelling rather than on a kernel type, so
they do not invert either.

## The fix that is available, and its cost

Structural inversion, made sound by verification rather than by trusting the
walk: find a constructor with a field whose *written* type is exactly the
parameter (`Cons(head: A, …)`), read the lowered field type at the matching Σ
position, un-shift it by the binders crossed to get there — and then **verify by
re-lowering** the declaration at the candidate arguments and comparing against
the type in hand. The verification is what makes a mis-read a decline instead of
a wrong answer, and it is why this is not a display one-liner: it needs the Σ
position arithmetic (payload fields only, container fields excluded) to be right
for every route, and re-lowering inside a display path wants a cost bound.

A parameter that occurs in *no* field's written type at all (phantom) is not
recoverable this way and would stay `<…>`.

## The other route, which is cheaper but narrower

Carry the *written* spelling of a binder's type alongside its name in `Cx`
(`Cx::push_skel` is the single funnel, so the vectors cannot desync), and print
that for a context entry. It gives the best possible answer — literally what the
user wrote — for the goal listing's context, and nothing at all for a type the
elaborator *computed*, which is the statement position and the `trivial`
mismatch. So it complements the inversion rather than replacing it.

## What it assumes from elsewhere

- **[[le-diagnostics-print-raw-el]]** owns the speller. Assumed here: only that
  it names an instance from the tag and prints `<…>` where the arguments would
  go.

## Log

- 2026-08-17: Second customer, from [[check-fallback-discards-expected-type]] (same day): the missing arguments are not only a display nuisance, they SUPPRESS a diagnostic. That round's mismatch report speaks only when the two types spell differently, because "this has type `And<...>`, but `And<...>` is expected here" reads as a compiler bug; so a mismatch whose whole difference is the type arguments falls back to the gate's bare `NotConvertible`. Recovering the arguments would turn those back into stated mismatches, which raises this from ergonomics to coverage. The reproducer is in that round's tests as a control (`a_mismatch_the_display_cannot_state_is_left_to_the_kernel`), so it will flip to a stated message when this lands -- expect to rewrite it then.
- 2026-08-18: 2026-08-18: Third customer, and a measurement. [[lgg-diagnostic-dumps-kernel-terms]] gave `display.rs` a term entry point (`spell_term_clean`) and the `cannot generalize` diagnostic now spells its goal — at **tier 0**. At a *recursive* declaration it still cannot: the value is `supf` whose shape annotation is a generated global, and `ctor_value` reads the nominal tag only out of an inline `Wf`/`Sum`/`Sigma`. The cheap route was tried and does not reach — `unspell_here` inverts a `#tycode` reference and a shape code is not one — so this is the inversion described above and not a lookup. Cost datum for whoever schedules it: the term speller is now public, so the missing piece is exactly the tag/argument recovery, with no printer to build first.
- 2026-08-20: Closed. The type-argument half takes the proposed verified
  inversion: exact parameter-typed payload fields provide candidates, each is
  strengthened out of the constructor telescope, and a complete candidate set
  is printed only when re-lowering reproduces the original constructor shape
  exactly. Diagnostic work is capped at 64 constructors-plus-fields; phantom,
  indexed, value-parameterized and oversized cases retain `<…>`. The existing
  suppressed `And` mismatch now states both nested instantiations, and open
  `List<A>` context entries print their actual argument. One earlier claim is
  corrected by implementation: the recursive `Wf` customer needs no structural
  inversion. Its `D#shape` is already registered with the exact inline shape,
  so a shape-specific inverse lookup recovers the tag without reduction; the
  recursive `Tree` congruence diagnostic now states its constructor-valued goal.
  `scripts/bench --check`: 106 comparisons within thresholds. Full
  `scripts/test`: 1980 passed, 0 failed.
