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

## Handoff (2026-11-26, end of the slice's third session)

**Done** (design note §25.9; on `claude/ownership-slice`, which has merged the coordinating branch at 320441e6 and the proof thread at 4bf882b):
- `Strs::Laid` from numbered instances: `SeqNum`/`WinNum`/`WinsNum` and `Seq::words_num`, `Seq::words_win_num`, `Seq::vec_num` at the end of `sequences.hthr` (which imports nothing of `placement*`, ever); `Strs::laid_of` in `placement_laid.hthr`; `KindNum` asks a record of words `RecLaid` directly (owed: derive it from `RecordLaws` when a record instance is placed).
- Probes: `strs_laid`, `list_not_laid`, `first_disagrees`, `ill_coded`, `mixed_reads_zero`, `death_breaks_rel` (F7's old statement), `cw_past_end`, `view_loop_refused`.
- F7 ruled: a cell over a dead block constrains nothing (`value_live` in `SlotHolds`); `slot_kill` beside `injects_kill`.
- `place` after the run's changes: no ownership tests, `PSlot` is code + ids, `Back`, `Len` at 64 bits, a word variable written whole rebinds, the `JCopy` `Yield` frame defect fixed. Seam: `ActWrites` in `StageRel` (in place of `SlotsWritable`), the `Act` threaded through the stage types, `StageBack`, `StageLen`; `WritesLent` is the entry premise only.
- Stages proved (`placement_stages.hthr`): `stage_lit`, `stage_death`; shared: `rel_push`, `rel_kill`, `holds_map`, `slot_of`, `word_slot`, `cells_at`.

**Next, in order**:
1. `StageOp`. `place`'s `Op` is now `PEnv::place_op`, an `and_then` chain: invert `hp` by `let h0: PEnv::place_op(…) = Some(o) = hp;` then `Option::bind_some` step by step (`Bool::guard_some` at a guard). Unification needs the equation's head to be the chain after one unfolding; `Stmt::place` itself does not unfold far enough. Then `slot_of` + `word_slot` for each operand (level 2 stuck where `Value::get` is `None`); the size guard gives `w = WBits(64)`; rewrite each `Dyn` to `Dyn(u64, Dyn::back(…))` (`Dyn::back_like`) so `Dyn::words` reduces; the codes agree by one named lemma from the guard (`sb.code.same(sa.code)`); the word by `BitVec::ofNat_toNat`; finish with `rel_push` and `Locals::agree_set`.
2. Refactor the other kinds the same way (`Test::place`/`PEnv::less`, `read_place`, `PEnv::locate`/`walk`, `View`, `Take`, `Back`, `Len`, `write_word`) and prove `StageTest` (64-bit unsigned comparison of zero-extended narrow words: needs `toNat` < 2^b ≤ 2^64), `StageTake`, `StageRead`, `StageView`, `StageBack` (the reference case is the identity; the copy case is the store), `StageLen`, then `StageWrite` (`put_image`, `injects_store`; the store allowed by `ActWrites` from `Act::may` in `Stmt::write_run`).
3. `StageRet`, `StageJump`, the packed join.
4. `PlaceComplete` is not provable yet: (a) the six code comparisons need either a lemma from the checker's code rule at each site or §26.5's run change that deletes them; (b) a loop answering a view is refused (`view_loop_refused`: the loop's results part is zeroed and a reference has no zero). Proposed to the coordinator: zero a reference by an `Offset` of a parameter's reference by a zero word. Await the ruling.

**Traps**: as before, and:
- `cong_fn` is at `Type` only: an equation over a kind or a window (`Type<1>`) goes through `cong_big` (placement_laid) or `j`.
- `Value::live` would clash (two `Value`s in scope): the function is `value_live`; `Slots::Below` cannot attach (no `Slots` type): `slots_below`; `split` is a keyword.
- Constructor patterns of `x86_64_call_contract::Value` are written unqualified (`Word(w)`, `Ref(_)`), expressions qualified.
- A collection literal in a motive needs `Cons(…, Nil)`.
- The untrusted evaluator runs out of fuel on full runs and on lowering sizes: read a size off the kernel with closed `n.leb(k) = True { refl }` probes.
- Suite: `HEATHER_PR_BASE=60d3371 scripts/test --pr`, no native gates.
- 2026-11-26: Second session: F1-F6 found and ruled (§25.8); the statement corrected in placement_seam.hthr (Strs::Laid and StrsLaws premises, arguments coded, images below 2^64, StageRel with codes and ids below next, leaf stages stuck-or-step), end_to_end re-checked; place compares codes as a marked interim; the injection's lemmas proved in placement_inject.hthr (locate_image, put_image, window_kept, injects_store, injects_kill). Suite at 4678039, HEATHER_PR_BASE=a7965e15 scripts/test --pr: == suite: 847 passed, 0 failed, 1 ignored ==. Handoff rewritten.
- 2026-11-26: Third session: Strs::Laid from numbered instances (SeqNum/WinNum in sequences.hthr, placement_laid.hthr's Strs::laid_of); F1/F2/F4 probes; F7 (StageRel vs a death of an owner) ruled (b), slot_kill; stage_lit, stage_death; merged 4bf882b and adapted place (three ownership tests gone, Back, Len at 64, word write rebinds, JCopy Yield frame defect fixed), ActWrites in StageRel, StageBack/StageLen; copy_window tests its lengths with Len (138 bytes vs 96 old). Suite at 7c2d5db, HEATHER_PR_BASE=60d3371 scripts/test --pr: == suite: 847 passed, 0 failed, 1 ignored ==.
