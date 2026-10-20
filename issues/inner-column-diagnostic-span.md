---
title: A missing constructor in an inner pattern column reports at the outer match's span
status: open
labels: [frontend,diagnostics,elaboration]
area: language
created: 2026-08-16
updated: 2026-08-16
---

Item 2 of [[diagnostics-name-the-written-form]], promoted on that issue's
closure (2026-08-16) so that the residue has an owner rather than keeping a
finished issue open (README rule 3). The **form** half of that issue is paid
everywhere; this is the **span** half, which turned out to be a separable
problem rather than the same fix.

The pattern compiler (`docs/nested-match-patterns-design.md` §3.4) expands a
deep pattern into a generated inner `match`, and gives it the *whole* match's
span, because the level it reports about has no source text of its own — the
user wrote a pattern, and a missing constructor there belongs to a **column**,
not to an arm. So:

```heather
fn f<A>(d: A, r: Res<Res<A>>) -> A {
    split r; on Stuck := d; on OutOfFuel := d; on Out(Out(v)) := v;
}
// error: `split` is missing an arm for `Stuck`, `OutOfFuel`
//   --> points at `split r;`, not at `Out(v)`
```

The message is *true* and now names the right form; it points one level too
far out.

## What a fix has available, and did not before

The column is not spanless. Every row's sub-pattern at that column carries a
`Span` (`Pat::span()`), and the arity-disagreement message beside it already
reports at one of them — `` `W` binds 1 field(s) in an earlier pattern of this
`split`, found 0 `` underlines the offending `W()` exactly. So the material
for a column span exists; what is missing is a decision about *which* span an
"the column is not exhaustive" message should carry, given that the fault is
distributed across the rows rather than located at one of them.

Candidates, none obviously right:

- the **join** of the column's sub-pattern spans — honest about the extent,
  but underlines several arms for one missing constructor;
- the **first row's** sub-pattern at that column — a concrete place to look,
  and arbitrary;
- the arm the user would have to *add* — which has no span at all, being the
  thing that is not there. This is the one that says what to do, and it is why
  the outer span was chosen in the first place: the fix is an arm at the outer
  match.

That last point is the reason to decide rather than to patch: it is not
self-evident that the inner span is an improvement, and
`a_deep_match_with_no_fallthrough_is_not_exhaustive`
(`crates/elab/tests/nested_match_patterns.rs`) pins the current behaviour, so
a change has to rewrite a test deliberately.

## When

Not triggered. The natural trigger is a real file where a deep pattern's
inner column goes non-exhaustive and the outer span sends its author to the
wrong place — a wide match with several deep arms, where "which column?" is
not answerable by reading.

## What it assumes from elsewhere

- **[[nested-match-patterns]]** owns the pattern compiler and the generated
  level. Assumed here: that the generated level stays generated — the fix is a
  span carried into it, not a source-level rewrite of what the user wrote.
