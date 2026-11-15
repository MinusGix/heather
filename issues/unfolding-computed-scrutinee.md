---
title: Unfolding equations for a decreases body that matches on a computed scrutinee
status: closed
labels: [frontend,elaboration,proofs]
area: language
created: 2026-09-05
updated: 2026-10-31
---



Residue of [[decreases-unfolding-equations]] (landed 2026-09-05,
docs/language/recursion/decreases-unfolding-design.md §3). The companion walk re-matches on a
*variable* scrutinee under a motive in which both anchors reduce into the arm;
a `match` on a **computed** scrutinee (`merge`'s `match nat::le_dec(x, y)`)
reduces neither anchor, so equating the arms would need the body rendered into
the motive twice, with its obligation references. `merge` therefore gets no
`merge_unfold` today (pinned as a negative control in
crates/elab/tests/decreases_unfolding.rs). Routes: generalize the scrutinee
(`match s as λ s => …` over a fresh variable with an equation, the same convoy
the lowering already uses for refinement) so the walk sees a variable; or
state the equation per outer arm. The first is the natural one.

## What it assumes from elsewhere
- **[[decreases-unfolding-equations]]** owns the walk. Assumed here: only that
  a variable-scrutinee `match` is in the fragment and a computed one is not.

## Log

- 2026-09-25: Hit again by the decimal spec in lib/decimal_line.hthr: `decimal(n)` by `decreases` over `match Nat::le_dec(10, n)` gets no `decimal_unfold`, so the spec is written with explicit fuel (`decimal_digits(n, n)`) instead. That's worth revisiting once this lands: the `decreases` form reads better as a specification.
- 2026-10-31: 2026-10-31: Now blocks R3b of [[pure-imperative-statements]]: a lowered while … decreases matches on its condition under an equation binder (docs/language/sequencing-surface-design.md §5.3), and its _unfold is refused because the lifted obligation depends on that equation (probe P5). The first route here, generalizing the scrutinee into a convoy, is the one the lowering needs.
- 2026-10-31: 2026-10-31: [[dependent-match-compiler]] would retire this as one symptom of the general fix (an equation in every arm, case trees with clause equations).
- 2026-10-31: Owned by [[unfolding-through-convoyed-match]] (slice 4 of [[dependent-match-compiler]], docs/language/matching/dependent-match-compiler-design.md §8): the walk re-matches the convoy's own eliminator at a fresh scrutinee with the equation as a binder.
- 2026-10-31: Closed by [[unfolding-through-convoyed-match]]: merge's negative control is now a positive test.
