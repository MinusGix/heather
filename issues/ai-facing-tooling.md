---
title: AI-facing tooling: every failure returns the search state that produced it, as data
status: open
labels: [tooling,design,meta,diagnostics]
created: 2026-08-05
updated: 2026-08-05
---

Direction issue, not scheduled — filed from the 2026-08-05 riff (while the
ergonomics round ran), so the design is written down rather than
re-derived. Premise: models working in Heather are already the norm, and
Heather is in no training data, so the tooling is the whole interface.

## The thesis this issue owns

**Every failure should return the search state that produced it, as
data.** One principle, several features, each with its own issue:

- Conversion failure -> a budget-bounded divergence trace (where the two
  sides split, after what unfoldings). Models handle such dumps far
  better than a casual human glance; humans get the prose summary on top.
- Resolution failure -> nearest names in scope.
- Solver failure -> the stuck state ([[grind-port]] owns the biggest
  instance).
- Statement before proof -> [[heather-disprove]].
- Discovery -> [[lemma-selection-and-search]].
- Measurement of all of the above -> [[proof-benchmark]].

Plus the loop primitive none of those work without: `heather check
--json` emitting decoded goals and diagnostics as data (the decode half
is [[goal-display-decodes]]; this adds the serializer), and eventually
`heather ctx <file> --json` — as modules grow, preserve today's
accidental virtue that everything in scope fits in a context window.

Two properties everything here inherits:

- **Truthfulness through the one resolution judgment**: anything a tool
  reports as reachable must resolve the same way elaboration does.
- **The kernel is the judge**: the elaborator is untrusted, so no tool
  output ever enters the trusted story; a wrong hint is a rejection.

## What it assumes from elsewhere
- **[[lsp-from-the-meta-layer]]** owns the editor-facing surface of the
  same information. Assumed here: only that the two share the
  serialization, not which lands first.
- **[[elaboration-determinism]]** owns reproducibility. Assumed here:
  only that programmatic scoring and stable dumps want it eventually.
- **Feedback latency** is owned by the perf accumulator issues; noted
  here only that agent loops multiply check time by hundreds, so they
  are quietly also AI-ergonomics issues.
