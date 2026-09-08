# Reusable callee execution summaries

`CallSummary` indexes a reusable postcondition proof by its exact instruction
list and stack-access model. The proof quantifies over the initial machine
state. It does not embed a chosen argument pair, memory contents, or entry RIP.

The current producer emits one summary for an opted-in source callee. Its
postcondition includes the source result, the native integer call contract,
and preservation of RSI. The last field is an additional guarantee of this
implementation: the two-call wrapper needs its original right argument after
the first call. It is not a general promise about scratch registers.

The source theorem accepts an arbitrary FunctionIR valuation and checked graph
witness, with input-register equalities. Each concrete caller supplies its own
valuation and witnesses. The second call's left input is connected to the first
call's result through the first summary and the source-denotation theorem;
its right input uses the explicit RSI-preservation fact. Short register equalities
carry the second result through the caller epilogue to the final exit request.

## Execution and placement

`CallPremises` contains concrete intermediate states, actual byte-fetch and
access obligations, and an equality from each state to the canonical functional
successor. The intermediate states are checked witnesses, not assumptions;
`call_premises_cons` assembles each edge through a generic checked constructor.
`call_run_checked` proves both a fetched machine trace and equality of its final
state to functional execution. `use_call_summary` transports the generic
postcondition to that final state.

Call sites supply these local placement premises and reuse the source/refinement
and execution-summary proofs. They do not repeatedly convert a whole symbolic
callee run into concrete states. `call_trace_append` connects each callee
execution to the surrounding caller trace. Fetch premises cannot be replaced
by a claim that the producer selected the right instruction.

An instruction's fetch proof quantifies over arbitrary stack contents with the
exact emitted file. A single checked file-byte observation supplies both
execute permission and byte contents. `call_file_read_split` uses the checked
header length and `list::nth_append_r` to obtain a code byte without traversing
the header again; page, offset, and code-byte premises remain explicit. Its call site instantiates that proof with the actual
memory's stack projection. The unchanged file projection is checked by
conversion; stack writes remain visible to stack reads and callee effects.
Ordinary states also name their register and flag fields directly. Their
successor equalities use generic instruction-layout lemmas checked over neutral
states. Each placement supplies its checked next RIP, and subsequent projections
need not traverse whole-machine execution wrappers.

The two-call example places identical leaf fragments at two different
addresses and resolves each CALL displacement independently. The summary is
shared by both placements. This subset has no internal PC-relative operands;
support for more general relocation forms requires additional obligations.

## A callee-owned frame

For the two-call example, the leaf saves its incoming RSP in R10, reserves eight
bytes, and stores its left argument there. R10 is excluded from the arithmetic
body's temporary-register pool. Loading the frame size already clobbers R11.
The leaf restores RSP from R10 and returns. The private bytes remain changed.

`WordPrefixWrites` describes the exact byte addresses of the store. The checked
word-write effects cover both raw stack reads and observable ELF memory reads.
`WordOutside` and `stored_word_preserves_return` prove preservation of the
return word. The caller separately discharges exclusion of its live local
from the callee footprint before reloading it. Access rights, underflow,
canonical addresses, and wrap conditions remain distinct obligations.

Concrete exclusion proofs build the footprint one byte at a time from checked
address differences. CALL displacement proofs use width-bounded ripple arithmetic
and checked transport lemmas to state results in the canonical add/sub operations.
This replaces the initial producer's staged increment/decrement chains.
The second store's proposed literal value is connected to the first
callee's result and checked source evaluation. These named intermediate facts
keep checking local without adding trusted arithmetic or changing kernel limits.

The example in `examples/x86-native/reused_callee.hthr` computes
`leaf(leaf(left, right), right) XOR (left XOR right)`. For inputs 21 and 1, its
intended exit status is 3, and the second private store leaves byte 22 at
0x401fe0. The live caller local is 20, distinct from both call results (22
and 23). This is a bounded compiler strategy for exercising the interface;
general spill allocation and arbitrary call graphs remain separate work.
The small right argument keeps this concrete acceptance example within the
current arithmetic evaluator's limits; the summary theorem itself quantifies
over arbitrary arguments.

## Validation

The Linux x86_64 integration test builds with an empty `PATH`, checks the
certificate, and runs the ELF with exit status 3. The certificate contains one
callee summary definition, two summary applications, two trace compositions,
and the final private-byte and stack-restoration claims. The focused integration
passes under the standard 4 GiB / 300 CPU-second limits (223.75 seconds reported
by the focused test runner after integrating ripple arithmetic and prefix lookup).

Focused controls cover neutral machine states and memory, all seven ordinary
field layouts, preserved return words, changed dead bytes, and a file fetch near
the end of a 512-byte fixture. Wrong bytes, invented successor states, missing
fetch evidence, incompatible postconditions, stale instruction lists,
overlapping footprints, and incorrect displacement results are rejected.

Final merge validation on 2026-09-08: plain `scripts/test` passed with
**2494 passed, 0 failed, 5 ignored**, including both native targets that hit the
CPU cap in earlier merge attempts. Extended kernel checks passed 333 tests;
the repeat `scripts/bench --check` passed all 106 comparisons. The host was busy,
so these are acceptance results, not a controlled performance comparison.
`scripts/issue check` and `git diff --check` are clean.
