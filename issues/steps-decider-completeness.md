---
title: Steps decider: apart after an open index, and semantic completeness
status: open
labels: [ownership,library]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-25
updated: 2026-11-25
---

`Steps::apart` (lib/lang/ownership/steps.hthr) compares only the first steps that differ. Two places are apart in more cases than it finds:

- **An open index followed by more steps.** `[SElem(x), SField(0)]` and `[SElem(y), SField(1)]` are apart whatever `x` and `y` are, and the decider owes `x ≠ y` (`open_then_more` in lib/_tests/lang/ownership/steps_tests.hthr). Two ways out: an obligation that is a disjunction (the indexes differ, or the rest is apart, decided when they are equal), or for single-index kinds (elements, keys) trying the tails first and answering yes with nothing owed when they are apart unconditionally. Both are sound by a case split on the equality of the two indexes' values; the second keeps obligations conjunctive.
- **Two kinds of step at one place.** A field beside an element is refused; in the value model no value is both a record and a sequence, so they are vacuously apart. Refusing is the intended answer for a checker (the source is ill-typed), so this may be a decision to record rather than a gap.
- **A general semantic completeness theorem.** Completeness is stated syntactically (`Steps::apart_closed`, `Steps::apart_at_difference`, `Step::apart_complete`), and each kind of refusal has a `¬Apart` probe at a value (lib/_tests/lang/ownership/value_steps_tests.hthr). A theorem that every refusal on closed, one-kind, jointly valid steps is `¬Apart` in the value model needs a value at which both places are valid, built from the steps; say whether package 3 needs it before building it.

## What it assumes from elsewhere

- **[[ownership-steps]]** built the decider and its soundness.
