---
title: A tier-1 match arm's recursive binder has no spelling
status: open
labels: [frontend,diagnostics,inductives,display]
created: 2026-09-06
updated: 2026-09-27
---

Found by the [[omega-measure-at-constructor-pattern]] design pass
(2026-09-06, docs/omega-measure-reduction-design.md §1.1 and "Filed
separately"). Inside a `match` arm the tier-1 lowering aliases the recursive
binder `t` to `nth^l(⟦D⟧; mᵢ; cs'; ι_t)` (docs/inductive-tier1-wf-lowering.md
§6.3), which reduces to `Fst(cs')` on the arm's neutral children tuple.
`spell_term_clean`/`spell_term_source` (`crates/elab/src/display.rs`) spell a
`Supf` through `ctor_value` but have no case for a projection out of a neutral
children tuple, so any route that has to *name* such a binder fails. It
surfaced as `omega`'s "could not spell a natural expression" on the un-lifted
retry of a `decreases` obligation; it is a display gap, not an `omega` one,
and that round leaves it unreached rather than fixed.

Fix shape: map the projection back to the arm binder's surface name, which
the elaborator knows when it builds the arm.

## What it assumes from elsewhere
- **[[inductive-compiler]]** owns the tier-1 arm aliasing. Assumed here: only
  that the binder is an alias for a projection, not a fresh variable.
- **[[omega-measure-at-constructor-pattern]]** owns the path that first hit
  this. Assumed here: only that after its round the lifted obligation is
  accepted, so the retry that reaches this spelling no longer runs on the
  reproducer.

## When
Triggered: the next diagnostic, `omega` render, or lint that has to name a
recursive arm binder and prints a projection or refuses instead.

## Log

- 2026-09-27: 2026-09-27: Probably seen again, not confirmed as this binder: in the read-until-EOF process proof ([[native-read-until-eof]]), `omega` inside a `Cons(chunk, rest)` arm of a theorem matching on its list parameter failed with "could not spell a natural expression" over a goal about `chunk.len()`. The workaround there is a Nat-only lemma (`eof_room`).
