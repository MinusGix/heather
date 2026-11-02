---
title: A nested bind in a non-tail match arm needs a join point, not a packaged match
status: open
labels: [frontend,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-11-01
updated: 2026-11-01
---

`let r = match c { True => (<- x) + 1, False => 0 }; rest` is refused with
"`match` in inference position needs a motive" (docs/sequencing-surface-design.md
§13 item 4). The lowering, shared with `?` (`crates/syntax/src/try_lower.rs`),
packages each arm with `Pointed::ret` and binds the match once, which makes the
match `Bind::seq`'s first argument, where nothing gives it a motive. `?` has
the same gap at a non-tail match (docs/result-propagation-design.md).

## Fix

Bind the continuation once as a join point, `let k = λ (r: T) => rest;`, and
call it from each arm, so the match stays in tail (checking) position:
§5.5 of the design note, Lean 4's join-point lowering. The join point's
domain needs the arm type: from a written annotation (`let r: Nat = match …`)
syntactically, or by the elaborator. R3's statement `if`/`match`
([[pure-imperative-statements]]) needs the same join points, so the two
should share it.

## Done when

The probe above checks without a motive, and `?` at the same shape does too.
