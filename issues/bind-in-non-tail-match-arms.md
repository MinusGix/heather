---
title: A nested bind in a non-tail match arm needs a join point, not a packaged match
status: open
labels: [frontend,elaboration,ergonomics]
area: language
milestone: [lang-sequencing]
created: 2026-11-01
updated: 2026-11-25
---

`let r = match c { True => (<- x) + 1, False => 0 }; rest` is refused with
"`match` in inference position needs a motive" (docs/language/sequencing-surface-design.md
§13 item 4). The lowering, shared with `?` (`crates/syntax/src/try_lower.rs`),
packages each arm with `Pointed::ret` and binds the match once, which makes the
match `Bind::seq`'s first argument, where nothing gives it a motive. `?` has
the same gap at a non-tail match (docs/language/result-propagation-design.md).

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

## Log

- 2026-11-25: A measured cost of the missing join point, from the ownership interfaces package ([[ownership-interfaces]], [[ownership-join-chain-cost]]). `return` outside a loop copies what follows into every arm that falls through (docs/language/sequencing-surface-design.md §22 items 5 and 8), so K statement `if`s in sequence, each holding a nested `if` with a `return`, elaborate to a term exponential in K. The source function alone, checked against itself by `refl` (kernel steps, width one, fresh cache): 2.1k, 5.4k, 12.3k, 26.4k, 55.6k, 116k at K = 1 to 6, about ×2.2 per join. The ownership meaning of the same body binds what follows once and its text is linear in K; the pin's cost is the source's copied term. Binding the rest once as `let k = λ … => rest` here would make both linear.
