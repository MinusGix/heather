---
title: Proof scripts are Tac blocks: goal combinators move from the grammar into lib/std/tactic
status: open
labels: [design,tactics,syntax,proofs]
area: tactics
created: 2026-10-31
updated: 2026-10-31
---

Item 4 of the fundamental-improvements memo of 2026-10-31 (Claude Doc, https://claude.ai/artifact/Y2Jo9y9Mgd52QdguvaL43s). Minus agrees (2026-10-31): the tactic language was built
for this, but it still needs work, and tactics still need converting.

Once [[binding-statements]] lands, a proof script should be a block over
the `Tac` carrier, and the built-in goal combinators (`split_all; all_goals
{ … }`, `z ⊢ apply …; give …;`, the parser's `goal_combinators`) become
library functions in `lib/std/tactic`:

```heather
theorem t(…): … by {
    let h <- intro("h");
    split_all();
    all_goals(omega);
}
```

Then tactic authors and proof writers use one language, and new combinators
(`repeat`, `first`, `focus`) need no parser change.

## Scope

- The goal model. `Tac<A>` focuses one goal and returns its proof `Expr`. A
  script transforms a goal list, as Lean's `TacticM` does. Decide between a
  goal-list state in `Tac` and a `Script` carrier over it.
- Re-express every built-in combinator in it, with the same goal semantics
  and nested-goal tests.
- Convert the built-in tactics that are still Rust-side, or record why each
  stays.
- Absorb [[tactic-composition-ergonomics]] (its concise forms become library
  functions).

## Done when

Built-in goal-combinator grammar is gone from `parser.rs`, every existing
script checks unchanged or through a mechanical rewrite, and a user-defined
combinator works with no parser change.
