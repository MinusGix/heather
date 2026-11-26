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
