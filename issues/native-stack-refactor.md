---
title: Refine the native program stack before the next process
status: closed
labels: [x86,native,design,refactor]
area: heather-in-heather
milestone: [hih-program-logic]
created: 2026-09-30
updated: 2026-10-20
---

The native program stack grew one process library per program (`wc -l`,
`wc`, `tr`), and each restated what the others prove: the layout four times
over plus a Rust mirror, the failure path, the read request and end-of-file
test, the chunk induction, histories, stored-byte lemmas and register
frames. Claims take 24 to 54 parameters, and a program author passes five
theorem names whose types nothing checks up front.

`docs/archive/native-architecture-review.md` is the survey and the plan: R0
(mechanical cleanup), R1 (relocatable read head and failure tail), R2
(bundled parameters), R3 (one read-until-EOF driver over a body contract),
R4 (one layout description shared with the producer), R5 (uniform piece
contracts, one typed generator), R6 (a checked program bundle, profile from
the source's types), R7 (one stored-bytes kit and emit-then-write tail).
Emitting stores ([[native-loop-emitting-stores]]) waits on R3, which makes
`tr -s`/`-d` a body for the driver instead of a new process.

## Log

- 2026-09-30: R0 and R1 landed (review §8): one SYSCALL encoding, the write loop's duplicate targets retired, io_entry named; the read head and failure tail proved once in elf64_read_pieces and used by the state and map processes and the write loop. R2 next when chosen.
- 2026-09-30: R2 landed (review §8): StateShape + StateLoop(shape), StateStart, per-piece jump-fact records with target lemmas, EofTail at an offset, PrintCodes + PrintFormat(codes) and FieldsCodes + FieldsFormat(codes), ThreeCounts/ThreeSpecs/MapByte; claims 33→18, 50–54→26–27, 24→14 parameters; producers emit each bundle once as a transparent fn. Records with dependent fields proved costly (split into data + proofs). R3 (the read-until-EOF driver) next when chosen.
- 2026-09-30: R3 landed (review §8): one read-until-EOF driver eof_from over EofStep<X>/EofEnd<Y> and an EofProcess (invariant framed by ReadKept, a chunk body with a continuation, a chunk ending, a tail); the state and map processes are instances; write loop's continuation is FinishedThen. Emitting stores (tr -s/-d) is now an EofProcess. R4 (one layout description) next when chosen.
- 2026-09-30: R4 landed (review §8): x86_64_layout (pieces + measured lens, layout_at by index, layout_resident, layout_len, JumpsForward/JumpsBack facts with jumps_forward/back and a shift for pieces at a symbolic offset); read head, failure tail, state, write loop, map, count and fields tails are layouts; sums, skips, spans and target theorems gone; producers keep one Layout table (native/layout.rs) with jumps named by label and fill the library's jump-fact records with refl; producer mutation control added. Executables byte-identical. R5 (uniform piece contracts) next when chosen.
- 2026-09-30: 2026-09-30: R5 landed (review §8): Computes<M, A> contract over a library-fixed scratch list (keeps records gone, a kept register is trivial), piece_runs/block_runs (PieceRan), the generator publishes {p}_computes and the typed generators share one implementation; then in-place loop fields, cursor and budget (copies gone, wc -l 654 → 630 B, wc 5946 → 5898 B). R6 (the author's surface) or R7 (output) next when chosen.
- 2026-09-30: 2026-09-30: R6 landed (review §8): a read program is one checked bundle, CountProgram(step, needle, spec) / FieldsProgram<C>(step, needle, init, counts, first, second, third) in function_ir_loop, facts as fields, refused at the author's source when wrong; LoopCountsAdvance for record advance; build-x86 takes the bundle's name (profile from its written type, byte map by type), per-program flags and the bounded_readonly wrappers gone; producer context module restates the facts before generation; count/fields producers share one skeleton; stdin-program test helpers shared in native_support. Executables byte-identical. R7 (output) next when chosen.
- 2026-09-30: 2026-09-30: R7 landed (review §8): one stored-bytes kit in elf64_io (pointwise Stored with store/kept/join/part/sends; wc -l's print_sends, wc's StoredList family and tr's byte-store facts replaced); R5's block_runs folded into R1's block_ran; one formatting spec: decimal_places over every width and field_is_decimal (field(n) = pad_left(7, ' ', decimal(n)) for n < 10^7), and wc's claim line is %7d over decimal. Not done: the restoring kit over the shift (omega needs literal constants) and cursor stores in the tails (belongs to the first emitting program). The review's R0-R7 are all landed; next is tr -s/-d (issues/native-loop-emitting-stores.md) when chosen.
- 2026-10-01: 2026-10-01: Programs are now written at their own step type, with routine obligations as bundle defaults: [[automatic-author-surface]]. The bundles moved to lib/read_program.hthr and the loop generator takes fold_body steps. The next process is the stream filter ([[native-loop-emitting-stores]]), and the unification the review deferred is [[native-one-program-logic]].
- 2026-10-21: R0-R7 all landed (2026-09-30), and the stack they refined is to be burned rather than refined further (docs/native-program-logic-design.md §3, [[native-burn-process-stack]]). Closed: nothing left in this issue's scope.
