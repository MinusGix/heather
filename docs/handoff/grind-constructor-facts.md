# Handoff: grind round, constructor facts (from Atelier, interrupted 2026-11-05 14:27 UTC)

Worktree at handoff: local Atelier worktree (now pushed; use the branch)
Branch: atelier/tactics-next-grind-round-5y3v3j (WIP commits pushed 2026-11-05; 5 behind origin/master at handoff)
Milestone tac-general. Owner issue: issues/grind-port.md; this round's issue: grind-constructor-facts. Design: docs/grind-design.md.
Old session (avoid resuming, ~470k context): 4f04f141-2115-4653-b47a-4b3bf16db576

## Goal
Pick the next grind capability from evidence (a library sweep), build it, and convert the library proofs it now closes.
The pick was constructor facts: injectivity and disjointness. The sweep found about 35 `Option::some_inj(…, trans(sym(a), b))`
sites and about 35 `absurd(trans(…))` sites outside lib/native.

## Done (committed)
- 79fff9bf: constructor state, disequality reading, injectivity/disjointness steps, a generalized goal (equations,
  contradictions, under binders). The Rust host side splits the `inj`/`absurd` builders so the host can call them on an
  elaborated proof. Nat's `Succ` is now treated as a constructor (before, grind read it as an opaque atom).
  All 7 probes close, including the issue's 3 done criteria; the grind test module is green with 21 expected refusals.
- e96ef9f7: whnf of opaque atoms; x86_64_fetch / x86_64_data_read proofs converted to `by grind()`.
- a8d0706f: `Spine` contracts head beta-redexes; grind has its own copies of laws (law names must resolve where the `by`
  is, so `Nat::succ_inj`/`false_elim` failed in modules that don't import nat/logic); x86_64_stack converted
  (all four branches of `StackForm::executes_respects_defined`).

## Last WIP (committed as de1af717 at handoff)
crates/elab/src/host.rs, lib/std/tactic/grind.hthr, lib/std/num/float/round_real.hthr,
lib/std/os/linux/linux_x86_64_determinism.hthr (~42+/20-). Untracked probes/t_*.hthr and probes/closure.py.
It was in the middle of a bug: converting the `round_real` disjointness sites (`absurd(trans(sym(a), b))` over Bool locals)
gives a wrong-type result. It ruled out `open_goal` as the cause and was reproducing it on one declaration,
looking at the `Request::Spine` handling in host.rs (~line 1790).
In linux_x86_64_determinism, `lists_read_alike` converted; `c_strings_alike` was reverted (it reads its `there`
hypothesis through a match the branch only partly refines, out of scope).

## Open decision for Minus
May std modules below the native stack import `grind`? Options: (1) anywhere grind's own imports allow (int, memory, x86,
os, kernel_model, itree); (2) recommended: x86_64_*, linux_*, kernel_model, itree, float, but keep int and memory
hand-proved; (3) keep the rule and only convert where the tactic library is already in the closure.
The thread went ahead with (2) provisionally (fetch/data_read now import grind). Confirm before landing.

## What's left
1. Fix the round_real wrong-type bug, then commit.
2. Finish conversions in the allowed modules (linux_x86_64_io, linux_world_co, kernel_runs, bitvec, itree, …) per the decision.
3. Rebase on origin/master, run `scripts/test --pr` (lib/ changed), update the issue log, push and open a PR.
Leave alone: crates/cli/src/native*, lib/native (another lane).
