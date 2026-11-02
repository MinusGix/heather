---
title: Opt-in interface definitions: clients reason through equations, not the body
status: open
labels: [frontend,elaboration,proofs,performance]
area: language
milestone: [lang-proof-modularity]
created: 2026-10-31
updated: 2026-11-02
---

Round P2 of `docs/compiler-milestones-proposal.md` (§6.3, §7): opt-in interface definitions.

## Scope

- `interface fn` (spelling per [[proof-modularity-design]]): its unfolding equations are generated, and outside its module neither the elaborator's conversion nor any tactic unfolds it at open arguments unless the proof says `unfold f`.
- Closed values still compute. The kernel is unchanged, and a proof that crosses the boundary cites an equation.
- Boxing through the pull API is unaffected, so a `runtime fn` setup still reads the body.
- Migrate one library module (the interval or native layout lemmas) and measure it with `--timings` and `scripts/perf ab`. Record whether early cutoff (`docs/module-interface-cutoff-design.md`) can use the boundary.

## Done when

The migrated module checks with fewer conversion steps, and one rule in `docs/proof-patterns.md` is retired or narrowed.

## Log

- 2026-11-02: Design note `docs/interface-definitions-design.md` (proposed): `interface fn` flag; withheld bodies outside the module as unglued neutrals in the elaborator's `Defs`, glued at saturated closed applications (the sealed-theorem mechanism, new trigger); `unfold f;` block statement; `f_unfold` and per-arm `f_unfold_<Ctor>` equations; universe-valued interface functions refused this round. §9 lists Minus's decisions before the build.
- 2026-11-02: Built (PR #378), with these changes to the design:
  - the kernel gate withholds too, because `refl` is decided only by the gate;
  - the escape is an `unfolding f` declaration clause, not `unfold f;`;
  - closedness forces the arguments.

  `Interval::neg/add/sub/mul/npow` are now interface definitions. Two `creal_interval` proofs cite arm equations, and probes are in `interval_tests`.

  `scripts/perf ab --source-patch` over `creal_interval` (3 cold samples) shows conversion counters flat (`conv_misses` +0.0%, `eval_delta_steps` +0.0%) and seconds inside the spread. The interval clients already reasoned through the `*_has` lemmas, so this migration saved nothing and cost nothing. The "fewer conversion steps" criterion is therefore not met by this module. The next candidate is a module whose clients convert at open arguments (the x86-64 layout lemmas).

  Early cutoff does not use the boundary yet (design §8): filed `interface-body-early-cutoff`.

