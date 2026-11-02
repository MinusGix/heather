---
title: Rewrite the library's hand equation convoys and applied-hypothesis matches onto match h: and refinement
status: open
labels: [stdlib,cleanup,match]
area: language
created: 2026-11-01
updated: 2026-11-01
---

The second half of [[match-motive-sweep]], split off on 2026-11-01. The sweep deleted the 818 written motives that `--review` judged redundant. Census of the 923 motives left in `lib/` (heuristic classification, script in the PR #318 thread):

- 292 arrow motives, not applied, with λ-wrapped arms;
- 241 applied matches: hand-carried hypotheses or generalized arguments, `(match … as λ … → … { … })(h)`;
- 203 dependent goals the lint could not drop;
- 168 hand equation convoys, `(…)(refl)`;
- 19 large eliminations (motives into `Type`).

The lint only tests whether deleting the motive, as written, still checks, so none of these were candidates. Two classes can now go further with a rewrite rather than a deletion:

- **Equation convoys** become `match h: e { … }` with the `λ h =>` dropped from each arm (§4, slice 1).
- **Applied hypotheses that are locals** become a plain match, with the hypothesis refined by §5 (slice 2), when every arm's `λ` binds the same names.

## Done when
A rewrite lint (or script) proposes both rewrites, it is applied library-wide behind the library gate, and the census is rerun.
