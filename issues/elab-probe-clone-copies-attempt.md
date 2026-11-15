---
title: Speculative elaborator probes deep-copy the declaration attempt: a fifth of cold elaboration
status: closed
labels: [elaboration,performance,representation]
area: language
created: 2026-11-02
updated: 2026-11-02
---

Stop speculative elaborator probes from deep-copying the declaration attempt. About a fifth of cold elaboration time goes to cloning and dropping it.

## Problem

`op_carrier_head` (`crates/elab/src/dispatch/operator.rs` ~282, ~305) probes each operator leaf on `self.clone()`, so that a failed candidate cannot leak goals or diagnostics. About a dozen other probes do the same (`lib.rs` ~1959, ~5191, ~5211, ~5259; `binding.rs` ~64; `host.rs` ~1569, ~2993, ~3183; `traits.rs` ~2788). The derived `Clone` deep-copies `DeclAttempt`'s `RefCell<Vec<…>>` logs (`crates/elab/src/attempt.rs`). One of them, `check_notes`, holds a `CheckNote` per checking site met so far, and each note carries a full `Cx` clone (`names: Vec<String>`, skeletons, aliases, type variables). So one probe costs O(sites so far × context depth) allocations, its drop costs the same again, and an operator chain probes once per leaf.

Measured with a gdb stack sampler on cold checks (`docs/surveys/data-oriented-survey.md` §0, §1):

- calc_parser: 15.8% of samples are in the probe's clone and 6.4% in its drop.
- lib/std/num + lib/std/tactic: 12.8% clone, 7.4% drop.
- 8.8–11.5% of samples are inside `CheckNote`'s `Cx` alone.

## Measured first step

`CheckNote { cx: Rc<Cx> }` is three lines: the field, its constructor at `lib.rs` ~6512, and one reader at ~8845 (`&*n.cx`). `scripts/perf ab --before/--after`, 3 interleaved cold samples, dev profile (optimized libraries), 2026-11-02 on the cloud box: `docs/showcase/calc_parser.hthr` went from 7.59 / 7.51 / 7.68 s to 5.98 / 6.24 / 6.10 s wall, **−20%, separate**. The kernel gate and peak RSS did not move, and 34 counter columns were identical across both binaries and every sample. A repeat run gave −21%, also separate. `ReflNote`'s `cx` is the same shape.

## Structural fix

A probe should mark the attempt, not copy it. Every `DeclAttempt` log is append-only within an attempt, and the goal arena grows by allocation. So `probe()` records their lengths and a discard truncates back to them: O(fields), not O(contents). `module_delta::JournalSlot` already works this way (a clone keeps only lengths). The per-attempt memos (`instance_matches`, `emitted_entries`) are pure caches; whether a discarded probe's entries stay or are truncated depends on their keys.

In [[elab-field-lifetimes-explicit]]'s lifetime groups, a probe is one more clone rule. It shares the committed world, policy and module pass (it must never get a pool of its own), marks the attempt, and copies only the dynamic scope. Once the groups exist, one `Elaborator::probe()` can state that rule and the dozen `self.clone()` probes all use it.

## What it assumes from elsewhere

- **[[decl-attempt-lifecycle]]** owns the attempt's reset and phases. Assumed here: only that the logs are append-only between `prepare` and `finish`, which the truncating probe relies on.
- **[[elab-cx-persistent-binders]]** would make every `Cx` copy cheap, `CheckNote`'s included. The first step here is the special case that pays most now.

## Log

- 2026-11-02: Second file, same A/B (3 interleaved cold samples, 2026-11-02, cloud box): lib/std/num/rat.hthr went 37.91 / 37.61 / 40.00 s to 35.72 / 36.64 / 36.71 s wall, −3.3%, separate. The kernel gate overlapped, and the same 34 counter columns were identical. rat is light on operator chains, so the win scales with how many operator leaves a file probes; calc_parser is the heavy case at −20%.
- 2026-11-02: First step taken: CheckNote and ReflNote hold Rc<Cx> (separate PR from branch claude/project-thread-1bpp32). scripts/test --pr: 2921 passed, 0 failed. The structural fix (mark and truncate the attempt) stays open here.
- 2026-11-02: Structural fix taken; closed. `Elaborator::probe(|| …)` (`lifetimes.rs`) runs a `&self` probe in place and cuts it back: each group gained a probe rule that destructures every field (`DeclAttempt::{mark, restore}`, `ModulePass::probe_mark`, `DynamicScope::cells`), the goal arena gained `checkpoint`/`restore` with an undo log for solutions and spellings written into existing goals, and `direct_dependencies` became a `DependencySet` rolled back by length (so search candidates no longer copy the set either). All nine `&self` clone probes use it. `scripts/test --pr`: 2942 passed, 0 failed. `scripts/perf ab --base origin/master` on calc_parser, 3 interleaved cold samples, cloud box: wall median 4.73 → 4.72 s (samples 4.68–5.08 vs 4.71–4.95), **no change**: #357's `Rc<Cx>` and #363's persistent `Cx` had already taken the measurable share (calc_parser was 7.6 s before them). One counter moved, `instance_match_calls` 4,148 → 4,025, because a probe's `instance_matches` entries now survive it (a clone dropped them); 35 columns identical. No residue: the one remaining whole-elaborator clone that is not a fork, `elab_instance`'s snapshot, is taken between declarations, when the attempt is empty.
