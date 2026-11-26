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

## Handoff (2026-11-26, end of the first slice session)

**Done** (design note §25, all on `claude/ownership-slice`):
- `place` (`lib/lang/ownership/placement.hthr`), the seam's statement and `end_to_end` proved, no axioms (`placement_seam.hthr`), the stage types of `PlacementSound`, `Func::fragment` and `PlaceComplete` (stated; false today by `word_write_r`).
- `Seq::words`/`Seq::words_win` with laws in `sequences.hthr` (additive).
- The three programs through every layer by `refl` (`lib/_tests/lang/ownership/placement_tests.hthr`); bytes compared (§25.3, §25.7); joins both of whose arms yield placed once (`packed_linear`).

**Next, in order** (the coordinator's rulings of 2026-11-26):
1. Prove, as stage lemmas (not inline), the parts the run changes do not touch: the injection's lemmas (what `Sel::locate` reaches is what the level-2 selection reads, its bytes the encoding's slice; a word stored at a located offset is the encoding of the put); then `StageLit`, `StageOp`, `StageRead`, `StageView`, `StageTake`, `StageDeath`, `StageTest`; then `StageRet` and `StageJump` for word results and parameters at fixed positions. A stage that shows the statement wrong is a finding: stop and send it.
2. When the coordinator says the run changes are merged (`Back(p, x)`, `Len(p, w)`, writability by the activation's lent references, the call binding a referring written slot to the argument's own cell): delete `place`'s three tests (`PEnv::keeps`/`jump_keeps`, `PSlot.w`'s refusal, the `Prov` write-back recognition); place `Back` (nothing for a referring view, a store for a word copy) and `Len`; rewrite the three bodies with `Back` and `Len` (`copy_window` gets its run-time tests back; re-run the byte comparison); add `StageBack`, `StageLen`; prove `StageWrite`, `StageCall`, `StageRoutine`; `word_write_r` becomes placeable and `PlaceComplete` can be attempted.
3. When the out-of-room work merges: `EndToEnd` carries `Site::Tracks`' escape (status 139 after a prefix), `stop_rooms` for `depth_rooms`, the floor premise.

**Traps**:
- Name clashes: `level2` and `x86_64_call_contract` both have `Value`, `Answer`, `Ran`, `Done`…; `body` and `bytes_level` both have `Body`, `Call`, `Read`, `Write`; `body` and `function_ir_lower` both `Place`. Qualify types (`level2::Heap`, `body::Place`); in patterns write constructors unqualified (a qualified constructor in a pattern is refused), in expressions qualified works. `Type::method` declarations need the owner unambiguous: use free functions.
- `λ`-bound `M: Type` cannot be written as `<M>`: make the theorem generic (`end_to_end_at<M>`) and infer `M` at the wrapper.
- The probes' placements are literal lists from a per-path linear scan (a scratch script, not in the tree). What the lowering asks of a placement is in §25.3; regenerate by evaluating `placed(...)` and re-planning when `place`'s output changes. `Program::lower` refusals are silent: bisect by lowering variants of the body.
- Never run a check or evaluation beside the suite: two overlapping runs killed library and native gates at their rails (§ none; just the rule).
- 2026-11-26: Joins both of whose arms yield placed once (packed_linear: 2 + 4k nodes); count_newlines' loop 171 bytes. Handoff written.
