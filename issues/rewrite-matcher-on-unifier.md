---
title: Rewrite's occurrence matcher onto the elaborator's unifier
status: open
labels: [unification,rewrite,elaboration]
area: language
created: 2026-11-03
updated: 2026-11-03
---

The rest of [[instance-conclusion-matched-first]]'s proposal
(docs/elaborator-principles-survey.md §4). Instance search now matches a
candidate's conclusion with the elaborator's unifier, and the tactic host's
`match_at` already did (`host.rs`, `unify_root` then a conversion check).
Rewrite's occurrence matcher is the one left: `rewrite.rs` `match_spine`
binds pattern variables syntactically, compares a repeated binder by
conversion, and defers what it cannot read, with its own policy for each.

## Proposal

Match a rewrite's left side with the same unifier (checked assignment, the
δ-lazy step at a head mismatch, guesses last), at the transparency rewrite
wants: keyed by head symbol first as today
([[rewrite-keyed-conversion-matching]]), then the unifier instead of
`match_spine`, then the conversion check rewrite already makes. A repeated
binder becomes an ordinary solved slot that a later occurrence meets
(`U::disagree`), and the deferred list goes.

## Acceptance

- Every rewrite in `lib/` still finds the same occurrences (a run that
  counts occurrences per call before and after).
- `match_spine` is deleted, or what is left of it states why the unifier
  cannot do it.
