---
title: Showcases have no harness: one manifest, a real gate for calc_text, and a retention rule
status: open
labels: [showcase,tooling,testing,cache]
created: 2026-09-19
updated: 2026-09-19
---

The showcase is the shop window and the only large client the parser library
has, but "how a showcase is checked" has never been set up — it was added file
by file, each to whatever harness was nearest. The cost is now visible in four
places, and `docs/showcase/calc_text.hthr` pays all four.

**1. `calc_text` is gated by nothing.** Of the 23 `.hthr` files under
`docs/showcase/`, every one is referenced by a test except `calc_text`, the two
generator *outputs* (`contextual_rewrite_generated`, `relational_generator_generated`)
and the two deliberately-unchecked idealized files. `scripts/perf` names
`calc_text` exactly once, in the error message saying it is **not** in the
corpus. So the largest and most advanced showcase is verified only when someone
remembers to run `heather check` by hand — 4:24 cold on the desktop that filed
[[showcases-predate-their-ergonomics]], and every round that edits it
(that issue, [[showcase-spec-relations-as-records]], [[sequence-parser-source]])
re-derives that fact first.

It cannot simply join `crates/elab/tests/showcase_calculator.rs`: that harness
replays semantic images under the debug profile inside the suite's 6 GiB
address-space rail, and this file needs more than 8 GiB cold in release. The
tier that fits is the release-CLI one — `crates/cli/tests/native*.rs`, already
skipped by `scripts/test --fast` — which is what this issue proposes.

**2. Four hand-maintained copies of "which showcase, over which search dirs".**
`crates/elab/tests/showcase_calculator.rs` (`STD` + `SHOWCASE`),
`scripts/perf`'s `CORPUS`, `scripts/check-tree-sitter`, and the shell blocks in
`docs/showcase/README.md`. Each carries its own copy of the `-L` list, and the
README's copy carries a `mkdir -p /tmp/calc && cp docs/showcase/calc{,_parser}.hthr`
dance — because `-L docs/showcase` also offers `parser_core.hthr` and a module
in two search directories is refused rather than resolved by precedence
(the same trap a probe directory hits, which is why `scripts/perf`'s corpus
carries a comment about it). A reader
following the README does ceremony; a script that forgets a dir gets a
resolution error that names neither cause.

**3. `calc_text` is un-cacheable, and the budget is not the fix.** Its image is
483 M syntax nodes against `ModuleImageLimits::max_nodes` of 256 M, so it is
never stored, a warm recheck is ~95 s however small the edit, and `--only` has
nothing to replay ([[check-only-no-stored-image]] owns that pair of facts).
What is new here is the *second* limit: `max_bytes` is 512 MiB, and the images
on disk run 63–93 MB for modules in the tens of millions of nodes, so an image
of this one extrapolates to roughly a gigabyte — over both budgets, not one.
[[semantic-image-over-budget-republished-every-run]] already raised this budget
once (16 M → 256 M) and closed with the conclusion that raising it again
"would trade a rejection for a slower decode", the size being a symptom owned
by [[elaborator-canonical-type-spelling]].

So this round **measures and files, and does not chase** (user, 2026-09-19):
publish the image once with both limits raised locally, record the encoded
size, the decode seconds and the warm-run total against the 95 s
re-elaboration, and put the three numbers on [[elaborator-canonical-type-spelling]]
as the cost of its defect at this file's size. The budget stays where it is
unless those numbers say otherwise.

**4. The image store has no retention rule.** `target/semantic-test-images/modules-v1`
in the main checkout is **9.6 GB** — dozens of near-duplicate 63–93 MB images,
one per dependency world, none ever removed. The Kairos filesystem has already
filled once from stale worktree targets, and a showcase round is a
dependency-world churner by nature (every edit to `lib/std` republishes the
suffix). A retention rule — keep the newest image per `(module, dependency
world)`, drop the rest on publish — belongs with the rest of this setup.

## What this round lands

1. **A showcase manifest**, one declarative list, as the single source of truth
   for name, path, search dirs and tier. Consumed by `showcase_calculator.rs`,
   `scripts/perf`'s `CORPUS`, `scripts/check-tree-sitter` and a new
   `scripts/showcase`.
2. **`scripts/showcase check <name>`** — resolves the `-L` set from the
   manifest, stages the copy the collision forces, and wraps the run in the
   `ulimit` discipline `CLAUDE.md` requires, so the README's shell blocks become
   one command and the ceremony stops being the reader's problem.
3. **A release-CLI gate for `calc_text`** in the `crates/cli/tests/native*.rs`
   tier, skipped by `scripts/test --fast`, asserting the file checks clean and
   a small number of its public results.
4. **Retention for the image store**, with the 9.6 GB measured above as the
   before.
5. **The three cacheability numbers**, filed, not acted on.

## What it assumes from elsewhere

- **[[elaborator-canonical-type-spelling]]** owns why the image is 483 M nodes.
  Assumed here: only that the size is its defect's symptom and not a fact about
  the file, which is why this round records numbers rather than raising a budget.
- **[[check-only-no-stored-image]]** owns the `--only`/over-budget diagnostic
  pair. Assumed here: only that an over-budget module is never stored, so the
  ~95 s recheck is the standing cost.
- **[[semantic-module-images]]** owns the image format and its limits.
  Assumed here: only that both `max_nodes` and `max_bytes` are the reader's.

## Sequencing

Ahead of [[showcase-spec-relations-as-records]] and [[sequence-parser-source]],
both of which edit `calc_text` and would otherwise each pay the "there is no
gate and no cache" tax again, and neither of which is blocked on it — this is a
harness round with no language surface in it, so the two can land in either
order if a reader would rather have the nicer spelling first.
