---
title: Report unreachable match rows and redundant `_` arms
status: open
labels: [frontend,elaboration,diagnostics]
created: 2026-08-05
updated: 2026-08-05
---



The pattern compiler ([[nested-match-patterns]],
`docs/nested-match-patterns-design.md` §3.4) computes neither redundancy nor
reachability, and both silences are deliberate rather than forgotten:

- a row shadowed by an earlier one never reaches a leaf, so its body is never
  elaborated — harmless (the hole pre-count is documented as an upper bound)
  and invisible;
- a `_` arm with nothing left to expand to is **dropped**, because the
  compiler emits redundant `_` arms itself (a `Nat` column already covered by
  `Zero` and `Succ`), so refusing one would have meant marking generated arms
  and the pass remembering which spelling produced it.

Both want the same thing, and it is the thing that does not exist: a
**warning** channel. `check_source` returns `Vec<ElabError>` and every
diagnostic is fatal, so "this is dead code" has nowhere to be said. Making
redundancy an *error* is the wrong trade — it turns a refactor that adds a
constructor arm into a build break at every `_` that used to cover it.

## What it assumes from elsewhere

- **[[nested-match-patterns]]** owns the pattern compiler. Assumed here: only
  that a generated `_` arm is indistinguishable from a written one, which is
  what makes "refuse a redundant `_`" unavailable without new bookkeeping.
