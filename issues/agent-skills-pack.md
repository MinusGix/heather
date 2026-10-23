---
title: Write agent skills for formalizing, proving and diagnosing in Heather
status: open
labels: [tooling,ai,docs]
area: infrastructure
created: 2026-10-23
updated: 2026-10-23
---

From the Arend survey (`docs/arend-survey.md` §6). Arend ships a skills
collection for coding agents (`github.com/sxhya/arend-skills`, paper §5):

- `arend-formalize`: a procedure from an informal statement to a file that
  type-checks with only `{?}` goals left: how to orient in the library with
  the CLI's retrieval flags, how to choose classes and lemmas to reuse, and
  in what order to work.
- `arend-prove`: filling the goals, with a catalogue of the metas
  (`rewrite`, `cases`, `simplify`, `equation`, `cong`, `ext`, `linarith`,
  …), their semantics, decision tables and common failure modes.
- `arend-quirks`: where Arend's syntax and semantics differ from what a
  Rocq, Agda or Lean user would expect.
- `arend-error-type-mismatch`, `arend-error-extraneous-input`: two families
  of misleading errors, where the reported mismatch or token is a
  downstream effect of an upstream name-resolution or parsing problem.

The two first skills form a pipeline, and the skills record newly learned
behaviour for later use.

Heather is in no training data and is developed almost entirely by agents
(`issues/ai-facing-tooling.md`'s premise), yet the equivalent knowledge is
spread over `CLAUDE.md` (test and run discipline), project memory (quirks
such as "an all-numeral relation like `0 < 1` silently means `Nat`", "prove
closed offset facts by evaluation, never by conversion", "error-path
diagnostics never spell a whnf"), design docs, and the issue files.
`.claude/` has no skills.

## What is wanted

A small set of skills under `.claude/skills/`, each a `SKILL.md` whose
description says when to load it:

1. **heather-formalize**: statement to a checking file. Where things live
   (`lib/std/<type>.hthr` owns that type's facts), how to find a lemma
   until `heather search` exists (grep conventions, `T::name` members,
   function-scoped theorem names), class binders and relation-indexed laws,
   and the capped `heather check --cache --only` loop.
2. **heather-prove**: the tactic catalogue (`omega`, `ring`, `calc`,
   `rewrite`, `subst`, `split_all`, `positivity`, `decide`, …) with when
   each applies and how each fails, plus "prove by evaluation" patterns.
3. **heather-quirks**: the surprises, collected from memory and closed
   issues, each with the issue that explains it.
4. **heather-diagnose**: reading a conversion failure, a `--timings`
   table via `scripts/timings`, and a run killed at the rail
   (`<stem>.open.tsv`).

Each fact in a skill links its owner (issue or design doc) rather than
restating more than a line, per `issues/README.md` rule 1, so the skills do
not become a second copy that goes stale.

## What it assumes from elsewhere

- **[[ai-facing-tooling]]** owns the tool outputs the skills drive.
  Assumed here: only that the skills describe today's CLI and get updated
  when it grows.
- **[[lemma-selection-and-search]]** owns search. Assumed here: only that
  heather-formalize's lookup section shrinks to "use `heather search`" once
  it lands.
