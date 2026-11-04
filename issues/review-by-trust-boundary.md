---
title: A PR review view by trust boundary: statements and kernel first, proofs collapsed
status: open
labels: [tooling,meta,review]
area: infrastructure
created: 2026-11-02
updated: 2026-11-02
---

`docs/agent-policy.md` §5 owns where review effort goes. This issue owns a
view that makes a large PR reviewable in that order.

Large PRs are mostly right, and reading all of one to find the rest costs
more than it should. In Heather most of a PR's lines are often proofs the
kernel has already checked; what needs a person is whether the statements
say the right thing, and the trusted Rust.

## The view

For a PR (or a local branch against `origin/master`):

1. **Statements**: every new or changed theorem, definition signature,
   axiom, class field and `runtime fn` contract in `lib/`, with proof
   bodies collapsed. Changed statements shown as a diff of the statement
   alone.
2. **Kernel**: every hunk in `crates/kernel/`, in full.
3. **Flagged**: hunks a reviewer thread marked as least certain, each with
   its reason.
4. **The rest**, grouped by kind (elaborator, compiler, tests, docs,
   issues) and collapsed under a one-line summary each.

Actions per hunk or statement: comment (sent to the thread that owns the
branch, with file and line), ask why, approve the section.

## Work

- Statement extraction from `.hthr` diffs. The tree-sitter grammar
  (`tree-sitter-heather/`) or the CLI's own parser can find declaration
  heads; a `heather` subcommand that prints a module's declaration
  signatures would serve this and the export work alike.
- The reviewer thread's flag format: path, line range, one-line reason.
- Where it lives: a tab in `scripts/issue serve` next to the Roadmap tab
  ([[area-notes-and-roadmap-map]]), or in Minus's own harness, reading the
  same extraction. The extraction is the part that belongs in Heather.

## Done when

A PR's statements and kernel hunks can be read on one screen, separate
from everything the kernel backstops.
