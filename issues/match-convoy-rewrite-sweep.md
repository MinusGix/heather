---
title: Rewrite the library's hand equation convoys and applied-hypothesis matches onto match h: and refinement
status: closed
labels: [stdlib,cleanup,match]
area: language
created: 2026-11-01
updated: 2026-11-02
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

## Log

- 2026-11-02: Done on PR #318 by script (rewrite, then whole-library check, then keep the hand form at each site the check refused, until the library checks). 125 equation convoys became `match h: e { … }`; 31 stay: those applied to more than `refl` (the match is then an application head, which needs its motive), `Tm::convoy` (rt's IfEq meaning reproduces its shape by `refl`), and sites the check refused (mostly native proofs whose goal unfolds through the scrutinee, a convoy under an unannotated `let`, and an equation named `code`, which is a keyword in that position). 67 applied-hypothesis matches on locals became plain matches with the hypothesis refined (bitvec, coitree_rec and memory kept most of the 21 refused). Census after merging master: 767 motives (303 arrow, 223 dependent goal, 181 applied with non-local or partial arguments, 44 convoys, 16 large eliminations).
- 2026-11-02: The lint's false reports on measure-generated matches are [[review-lint-redundant-motive-on-generated]].
