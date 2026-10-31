---
title: Opt-in interface definitions: clients reason through equations, not the body
status: open
labels: [frontend,elaboration,proofs,performance]
area: language
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-10-31
---

Round P2 of `docs/compiler-milestones-proposal.md` (§6.3, §7): opt-in interface definitions.

## Scope

- `interface fn` (spelling per [[proof-modularity-design]]): its unfolding equations are generated, and outside its module neither the elaborator's conversion nor any tactic unfolds it at open arguments unless the proof says `unfold f`.
- Closed values still compute. The kernel is unchanged, and a proof that crosses the boundary cites an equation.
- Boxing through the pull API is unaffected, so a `runtime fn` setup still reads the body.
- Migrate one library module (the interval or native layout lemmas) and measure it with `--timings` and `scripts/perf ab`. Record whether early cutoff (`docs/module-interface-cutoff-design.md`) can use the boundary.

## Done when

The migrated module checks with fewer conversion steps, and one rule in `docs/proof-patterns.md` is retired or narrowed.
