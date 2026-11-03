---
title: Merge issue and area-note bookkeeping without review
status: open
labels: [tooling,meta,tracker,ci]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

`docs/agent-policy.md` §6 owns which changes are bookkeeping and merge
without review: `issues/*.md`, area notes' observation and health fields,
and committed generated summaries. Decisions (design docs, the roadmap's
tables and log, the policy, `CLAUDE.md`) keep a review. This issue owns
making bookkeeping land without the ceremony.

`CLAUDE.md` already says docs-only and issue-only changes need no suite, so
the PR has no reviewer and no gate today; it only adds a round trip and a
merge race between threads that file issues at once.

## Options

1. **An auto-merging workflow.** A GitHub Actions workflow on
   `pull_request` that lists the PR's changed paths and, when every path is
   bookkeeping, runs `scripts/issue check` and merges it (or enables
   auto-merge). The repository has no workflows yet (`.github/` is absent),
   so this is the first, and needs a token with permission to merge.
   Keeps a PR per change as a record.
2. **Direct push with a path check.** Threads push bookkeeping commits to
   master; a check (a pre-push hook in the repo, installed by
   `scripts/session-start`, or a server-side rule) refuses a push whose
   diff leaves the bookkeeping paths. Faster; less trail.

Leaning (1): the record matters when a thread's bookkeeping is wrong, and
GitHub's merge button never runs a custom merge driver anyway
(`issues/README.md`), so per-issue files are what keep conflicts rare.

## Work

- The path list as one file the workflow and `check` both read, so the
  policy and the tooling cannot drift.
- A mixed PR is left for review, with a comment saying which paths made it a
  decision.
- A thread's guidance (in `CLAUDE.md`) to put bookkeeping in its own commit
  or PR when it wants it to land fast.

## Done when

An issue-only PR merges with no human action once `scripts/issue check`
passes, and a PR touching anything else does not.
