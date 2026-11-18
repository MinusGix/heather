---
title: The optimizer's search is half of a SHA-256 compile, and the linked gate needs the long CPU rail for it
status: open
labels: [native,optimizer,performance,testing]
area: heather-in-heather
created: 2026-11-17
updated: 2026-11-17
---

`compile-x86` of a linked SHA-256 export spends about half of a warm compile in the optimizer's reads (the `find_*` evaluations of `crates/cli/src/native/verified.rs::optimize`), and the linked-code gate (`crates/cli/tests/native_linked.rs`) runs three such compiles, each a process under the suite's CPU rail.

How it got here:

- The standard identities on by default and the search through a word's spellings (`spellings := 8`) put the three compiles at 75 to 95% of the 300 s rail over a cold store: [[master-red-2026-11-16]], [[master-red-2026-11-17]].
- The stage that puts new words (`Function::find_helped`) adds one plain walk per function that asks. On SHA-256 that is about a twelfth more evaluator steps over all reads, and the compiles then end at the rail. Before it was confined, the same piece cost a quarter more: regrouping work ran in every searching walk.

The gate has the 900 s rail of the other native tool gates for now (`CPU_RAIL_OVERRIDES` in `scripts/run-test-targets.mjs`, and `scripts/test`). This issue is what brings it back.

Where the steps go (`HEATHER_READ_TRACE=1`, summed by the stage letter of each read; shapes, the trace gives the numbers):

- The searching walks (`find_learned` with spellings: the reads lettered `l`, `p3`, `x0`, `x3`, `z`) are the largest share, and each function gets four or more of them: after inlining, after its tests, after the joined loads, after the stores.
- `find_guarded` (`g`) is next and does not search.
- Each walk is a fresh evaluation: nothing a walk learned of a function is kept for the next walk of nearly the same function.

Routes, cheapest first:

1. Walk less often: a searching walk after a stage that changed nothing a rule reads finds nothing. The driver could ask a stage what it changed, or search only the nodes downstream of what was put.
2. `Seen::spellings_through` re-closes a node once per other spelling of each operand; with the commuted spellings that is most of a node's work and nearly always finds the node's own closure again.
3. Collect what `find_helped` asks for in a walk the driver already runs (`find_worded` reads `Wants` the same way).
4. The e-graph of §9.4 in `docs/native/optimizer-rules-design.md`: classes shared across the whole function, built once.

Measure with `scripts/perf ab` on a SHA-256 export's `compile-x86`, and with the gate's own CPU figures in the suite's "processes past 60% of their own CPU rail" section.

## Log

- 2026-11-17: 2026-11-17: the reads now run on the untrusted evaluator (`crates/run`, `docs/infrastructure/untrusted-evaluator-design.md`), since profiling showed the cost was the kernel's evaluator doing an interpreter's work (glue, motives, an arena that frees nothing) and, inside the walks, `NatMap` gets and sets over `Nat` arithmetic, not rule matching. On SHA-256's compress every read runs there and the assembly is unchanged; the reads' share of a compile over warm modules fell from the largest part to about a quarter. What is largest now is not the search: each stage's output is spelled as text and elaborated again (the `opt_made_*` modules), some of them twice. The rule tables are also indexed by node kind (`ByKind`), a small gain. Routes 1 to 4 above still apply to what the walks cost on the new machine. The gate keeps its 900 s rail until the stage re-elaboration is cut.
- 2026-11-18: the stage re-elaboration is cut. A compile's reads share one untrusted machine (`heather_run::Session`), each stage is a value defined from its search (`found_made`), the driver reads `found_kind` and spells only the stages the certificate keeps (untrusted-evaluator-design §3.1). On SHA-256's compress the assembly is unchanged and a compile over warm modules lost about a third; what is left splits roughly evenly between the reads, the certificate stating each kept stage's function, and loading. `Nat::low_bit` joined the named arithmetic: the map recursed through it over a whole key.
- 2026-11-18: the certificate's stated functions were slow for a reason of the elaborator's: every `[…]` ran the collection-literal protocol whole (a resolution, two projections, their reductions), a thousand times a function. The protocol's answers are now remembered per scope (`Memos::collection_memo`), the term built is the same, and SHA-256's compress compiles within the bar over warm modules. What is left is the reads (`found_kind` spells both functions to compare them) and loading. The linked gate over a cold store is still past the 300 s rail, so its 900 s stays.
