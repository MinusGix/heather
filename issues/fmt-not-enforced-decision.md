---
title: cargo fmt is not clean and not enforced: record the decision
status: open
labels: [meta,tooling]
area: infrastructure
created: 2026-08-06
updated: 2026-08-06
---

Noticed twice in one day by managed rounds (2026-08-06): `cargo fmt
--check` reports ~2732 diffs and there is no `rustfmt.toml`, so agents and
new contributors must infer the house style by eye, and any future
`--check` gate would trip on the whole tree at once.

Either commit a `rustfmt.toml` that matches the existing style (and take
the one-time reformat commit, which will pollute blame unless done with a
`.git-blame-ignore-revs` entry), or record in `crates/kernel/DESIGN.md` /
CLAUDE.md that fmt is deliberately not enforced and "match surrounding
style by hand" is the rule. The current state — unenforced and unstated —
is the only wrong option, because every round re-discovers it.

## When

The next time a formatting disagreement actually costs a review cycle, or
before any CI gate is added.
