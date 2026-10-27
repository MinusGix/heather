---
title: Search the library by type: heather search, exact? and apply?
status: open
labels: [tactics,tooling]
area: tactics
milestone: [tac-general]
created: 2026-10-27
updated: 2026-10-27
---

Finding a lemma means grepping `lib/` by name and guessing its spelling. The
interval rounds spent many rounds of `grep -n "^theorem Rat::"` to find
`Rat::le_add_shift`, `Rat::inv_succ_mul` and `Rat::abs_le_natAbs`, and an
existing lemma is easy to re-prove by accident (`facts-live-in-their-type-file`
exists partly for this reason).

Wanted: search by type (Lean's `exact?` / `apply?`, plus a `heather search`
command).

Scope:

- `heather search '<type pattern>'` over a checked world: it lists
  declarations whose statement unifies with the pattern, metavariables
  allowed (`?x + ?y <= ?y + ?x` at `Rat`), modulo the carrier's designations,
  with module and line;
- a tactic `exact?` that tries each candidate whose conclusion unifies with
  the goal, closes the goal by any one that checks, and reports the term it
  used so the user can paste it. `apply?` does the same and lists what remains
  open;
- an index built from module images (`crates/cache`), so a search does not
  re-elaborate. Conclusions are keyed by head symbol and carrier, so the
  unifier runs on few candidates;
- output also as data, for agents (`ai-facing-tooling`).

## What it assumes from elsewhere
- **[[ai-facing-tooling]]**: the data form of the results.
