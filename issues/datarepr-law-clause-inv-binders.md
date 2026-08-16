---
title: A law clause has to spell the inv hypotheses it ignores
status: open
labels: [design,frontend,ergonomics]
created: 2026-08-16
updated: 2026-08-16
---

`docs/datarepr-design.md` §1.4 note 5, filed standalone after the note's
friction became duplication rather than noise
([[true-prop-trivial-hypotheses]] half 1, 2026-08-16).

A per-constructor law's statement quantifies over the repr's `inv` at every
recursive argument, so a hand-written law clause must bind those hypotheses
even when it never uses them. The note already records the obvious fix and
defers it: let a clause be **applied to the binders the statement quantifies
over** rather than checked against the whole Π.

What made it visible: a law's hypothesis is the repr's OWN `inv`, and two
trivially-inhabited `inv`s are not convertible with each other. Before the
defaulted `inv` became the prelude `True`, `BinNat` (which writes
`inv := bin_inv`, an equation) and `BinMin` (which takes the default) could
share one `bin_succ_abs_law` because both hypotheses were `Zero = Zero`.
They no longer can: `crates/elab/tests/support/mod.rs` now carries
`bin_succ_abs_law` (h0: (Zero = Zero)) and `bin_succ_abs_true` (h0: True) —
the same theorem twice, differing only in a binder neither body mentions.
That is one fixture, not a user report, but it is the shape any two reprs of
one spec type will hit.

Not the same want as default argument values ([[named-arguments]], this
issue's half-2 sibling): defaults fill an argument at a CALL, this fills a
binder at a DECLARATION. Neither implies the other.

## What it assumes from elsewhere
- **[[true-prop-trivial-hypotheses]]** owns the defaulted `inv`. Assumed
  here: only that a repr's `inv` is whatever its own clause says, so two
  reprs of one spec type can disagree on it.

