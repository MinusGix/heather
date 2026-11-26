---
title: Ownership: the level-2 to bytes-level seam stated, and three programs through every layer by evaluation
status: open
labels: [ownership,library,native]
area: heather-in-heather
milestone: [nh-ownership]
created: 2026-11-26
updated: 2026-11-26
---

Three layers of the new design exist and are proved or being proved separately: the checker with its level-2 run (`lib/lang/ownership/`, `SafeAt`), the bytes level (`lib/native/bytes_level/`), and its lowering to x86-64 with the call contract. Nothing has gone through all of them. The seam between level 2 and the bytes level (§16's package 6: layout and `placement_sound`) has no statement yet, and it is the seam that says whether `SafeAt` concludes what the back half needs. This issue writes that statement and carries three programs through every layer by evaluation, before anything is proved over it. Design note §24; §15.5, §15.9, §17.3, §18.3 and §19 are what it builds from.

## Scope, in order

1. **The statement.** A translation `place` from a checked function (this fragment: words, records of words, sequences of words and bytes; no holes) to a bytes-level routine, with each object's layout read from its code through the structures (`Strs`), and the theorem's type, `placement_sound`: under an injection of level 2's heap into the bytes level's, the bytes level's run at related arguments answers what level 2's run answers, at fuels related as stated. Then the composed statement, as a theorem that takes `placement_sound` as a hypothesis and is otherwise proved from what exists: a pinned, checked function's x86 code, run from a state injecting its arguments, returns the source function's value (`CheckSound`, `placement_sound`, the lowering's `Tracks`, `RunsAsMeaning`). If that theorem does not typecheck, the mismatch is the finding.
2. **Three programs by evaluation**, each from its reflected body: a loop over a byte buffer that only reads (`count_newlines`); a function that lends a window to write (`copy_window`); a recursion (`sum`). For each: the checker's verdict by `refl`; the pin to a source function by `refl`; the level-2 run and the bytes-level run of `place`'s output agreeing at closed arguments; `Program::lower` answering `Some`; the bytes compared with today's export row through `scripts/bytes-level-compare`.
3. **Report to the coordinating session before proving anything**: the statement, the three programs' results, and everything in `SafeAt`, the run, the body or the bytes level that had to be read differently for the seam to fit (fuel on the two sides, a `Jump` function against the bytes level's `Loop`, where a block's bytes come from, what `Lendable` and the `Loan` each ask).

## Not here

Proving `placement_sound`; the allocator and deaths (packages 6's second half and 8); objects with holes; the surface and the reflector.

## Done when

The composed theorem's type is written and checks with `placement_sound` as its one hypothesis, the three programs lower by evaluation with their bytes compared, and the findings are ruled on.

## Log

- 2026-11-26: Statement and the three programs landed (design note §25). `placement.hthr`: `place`, a checked body as a bytes-level routine, layouts from codes through `Strs`. `placement_seam.hthr`: `HeapInjects`, `value_lower`, `PlacementSound`/`PlacementSoundAll` (no hypothesis about the program: a translation theorem), `EndToEnd`/`EndToEndAll` (from `PlacementSoundAll` and `CheckSound`; it typechecks). `placement_tests.hthr`: `count_newlines`, `copy_window`, `sum`, each with verdict, closed pin, `place`, level-2 and bytes-level runs agreeing, `Program::lower` = `Some`, all by `refl`. Bytes against the export rows: count_newlines loop 273 → 219, caller 18 → 15; copy_span 217 → 123, copy_window 96 → 39 (no bounded-loop counter, no guarded load, the window tests are preconditions; paid: self-copies of references, the flag's comparison per pass, the copied tail). Thirteen findings in §25.4, the main ones: `SafeAt` says nothing of a run's internal calls, so `place` checks the written-sequence convention syntactically; level 2 has no writability, so `place` refuses a store not reaching a write-lent parameter and `WritesLent` is the premise; fuel is a bound (exact without calls inside a loop pass); the loop's exit bit must come from a comparison; `Bytes(n)` has no windows and `List<A>` a number index. Reported to the coordinating session; nothing is proved over `place` before the ruling.
- 2026-11-26: After the ruling (§25.5, §25.6): `Seq::words` with windows and its laws added to `sequences.hthr` (additive), the probes on it and lawful; `end_to_end` proved, no axioms (`safe_below`, `place_len`, then `SafeAt`, `PlacementSound` and `lower_program_tracks`; the program's functions are the list's by definition, every index checked, no primitive); `place`'s refusals sorted, a narrow index and a taken word answered back now placed, one checked in-fragment program refused (a word variable written), `Func::fragment` and `PlaceComplete` stated; the stages of `PlacementSound` stated as types, each concluding in the bytes level's claim for its form. Waiting on the run's three changes (items 2, 3, 8) before deleting `place`'s tests and proving the stages.

## Handoff (2026-11-26, end of the slice's fourth session)

**Paused at the owner's request.** Where it stopped:
- F8's clause has landed.
- Proved: `stage_lit`, `stage_death`, `stage_op`, `stage_test`, the whole-variable cases of Take and Read, and the walk (`walk_sound`).
- The wider-element probe is added (`placement_widths_tests.hthr`).
- The coordinating branch (123dec90) is merged; nothing in `placement*` changed.
- No work in progress outside the tree.
- The suite run at `HEATHER_PR_BASE=123dec90` was stopped before it finished, so the head has had no suite run. The modules and probes check one by one with `heather check --cache`.

**Done** (design note §25.10; on `claude/ownership-slice`):
- Stages proved:
  - `stage_lit`, `stage_death`, `stage_op`, `stage_test` (in `placement_stages.hthr`).
  - The whole-variable cases of Take and Read: `take_whole_goal`, `read_word_goal` (in `placement_places.hthr`).
- The walk, whole: `walk_sound` (in `placement_walk.hthr`), with its element, window and field steps, the atom (`atom_sound`), the scaled index (`scaled_ran`), the byte round trip (`round_bytes`) and the injected load (`load_injected`).
- `place` refactored into named steps, one inversion lemma per step: `place_op`, `less`, `atom`, `walk_step`. This is a trap too, see below.
- `scaled` fixed. `placement_widths_tests.hthr` covers 64-, 32- and 16-bit elements (the 16-bit one does not lower: `MOVZX r, word`).
- F8 ruled (a): `SlotHolds` says a word slot's cell is plain.

**Next, in order**:
1. **Read through a reference** (`read_place`'s `Cons` case; Take's `Cons` case is the same leaf with the same run, `read_go`).
   - The start, `walk_root`. From `slot_of` and the root cell's `Refer(rho)` over a live block:
     - `WalkAt(rho.b, o.val, rho.sels, Walk(Nil, r.id, len, s.code, next), c0, next, c0)`;
     - the slot's `read_values` equals `Ref::lower`, which gives the reference and length ids;
     - the code clause gives `rho.sels` fits.
     - One gap: the reference id is bound only where `Ref::lower` is `Some`, so either prove `locate_of_fit` or ask the coordinator for the `SlotHolds` clause (§25.10, last paragraph). I asked in the report.
   - Then `walk_sound` gives the reference to `inj(b)` at `Sel::locate`'s offset.
   - `locate_image` gives the window of the block's bytes, which is `word_bytes_at(size, index X)`.
   - `load_injected` and `round_bytes` give the word: `ofNat(index X)`. Get `X`'s width from `Width::sized` and its bound from `toNat_lt_pow` via `Dyn::back_like`.
   - Finish with `rel_push`. Level 2 is stuck where `Heap::val` is `None` or the selections do not fit.
2. **`StageView`**: the walk's reference and length word, with the new slot `[ref_id(at.place), word_id(len)]` lowering through `Ref::lower` of `rho.narrow(...)`; `Ref::narrow`'s selections are `rho.sels ++ Steps::sels`. **`StageLen`**: the walk's length word. **`StageBack`**: the reference case is the identity; the copy case is `write_word`'s.
3. **`StageWrite`**: the walk, then `Store`; `put_image` and `injects_store`; the store allowed by `ActWrites` from `Act::may` in `Stmt::write_run`. Refactor `write_word` into named steps first.
4. `StageRet`, `StageJump`, the packed join; then what is left of `PlacementSound` (the call, the routine, the fuel induction).

**Traps**: as before, and:
- **Never invert a chain in one proof.** Nested `Option::bind_some` matches or lets re-type every earlier step's equation at each level (exponential kernel cost). Write `place`'s code as named steps, define callees first (no forward references), and invert one step per lemma, each a single `match ... as λ _ => Goal { Exists(x, p) => ... }`.
- `omega` cannot substitute `size = 2` into `x * size`: rewrite the hypothesis with `j` first. It also needs a `let` name for terms such as `x.shift_left_one()`.
- `Var(w)` as an expression resolves as the type `Var`; write `Atom::ix(Var(w), ...)`.
- `x86_64_memory_contract::{Loc, Slot}` clash with `body`/`store`: qualify them.
- Records with parameters are built positionally (`WalkAt(ran, mem, ...)`), the parameters inferred from the expected type.
- `heather check --cache` is fast (seconds) once a run has stored the module. A run that aborts at the rail stores nothing, and the next run re-elaborates every import (minutes).

- 2026-11-26: Second session: F1-F6 found and ruled (§25.8); the statement corrected in placement_seam.hthr (Strs::Laid and StrsLaws premises, arguments coded, images below 2^64, StageRel with codes and ids below next, leaf stages stuck-or-step), end_to_end re-checked; place compares codes as a marked interim; the injection's lemmas proved in placement_inject.hthr (locate_image, put_image, window_kept, injects_store, injects_kill). Suite at 4678039, HEATHER_PR_BASE=a7965e15 scripts/test --pr: == suite: 847 passed, 0 failed, 1 ignored ==. Handoff rewritten.
- 2026-11-26: Third session: Strs::Laid from numbered instances (SeqNum/WinNum in sequences.hthr, placement_laid.hthr's Strs::laid_of); F1/F2/F4 probes; F7 (StageRel vs a death of an owner) ruled (b), slot_kill; stage_lit, stage_death; merged 4bf882b and adapted place (three ownership tests gone, Back, Len at 64, word write rebinds, JCopy Yield frame defect fixed), ActWrites in StageRel, StageBack/StageLen; copy_window tests its lengths with Len (138 bytes vs 96 old). Suite at 7c2d5db, HEATHER_PR_BASE=60d3371 scripts/test --pr: == suite: 847 passed, 0 failed, 1 ignored ==.
- 2026-11-26: Third session, handoff: place's Op as an and_then chain (PEnv::place_op) with Option::bind_some for inverting place; slot_of, cells_at, word_slot; rulings recorded (Len at 64, PlaceComplete waits on §26.5 and loop exits, view_loop_r in bytes-level-loop-exits). Suite at f31b6f6, HEATHER_PR_BASE=60d3371 scripts/test --pr: == suite: 847 passed, 0 failed, 1 ignored ==. Handoff rewritten.
- 2026-11-26: Fourth session (paused): StageOp, StageTest, the walk, the whole-variable Take and Read proved; scaled fixed with a width-varied probe; F8 ruled (a) and landed; 123dec90 merged. Suite not run at the head (stopped at the pause).
