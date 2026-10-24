# Bounded read-only loop contract

> **Partly burned in B2 (2026-10-24).** The loop contract (`function_ir_loop`) stays; the
> source reflector and the native loop certificates this document refers to were deleted
> with the per-function certificate path (`docs/native-program-logic-design.md` §3.2).
> Loops reach the verified lowering through `issues/function-ir-verified-loop-planning.md`.
> The last commit with the code is `82521eab`.

The source/IR contract lives in `lib/native/function_ir/function_ir_loop.hthr`. It is a semantic
interface for a bounded loop region, before physical selection. Source programs
use `bounded_readonly`; the elaborated-body reflector recognizes that resolved
operation, retains the checked step definition's qualified identity, and emits
a typed region plus a kernel-checked equality with the actual source function.
There is one evaluator, `loop_run`, for both source and IR meaning.

This does not yet insert a loop into the existing raw `StructuredRegion` node
family. That family currently admits fixed-width dataflow, conditionals, and
composition of structured producers with continuations;
`ReadonlyLoop<C>` specifies the typed loop interface that native selection must
realize. In particular, a checked step reference is not evidence that its body
has been selected into machine instructions.

## Source interface and representation

The first reflected fragment is a transparent definition with five parameters:

| Parameter | Representation | Meaning |
| --- | --- | --- |
| buffer | `ReadonlyBytes` | Caller-owned source identity, base, length, read outcome function |
| needle | `BitVec(8)` | Immutable byte supplied to each step |
| budget | `Nat` | Maximum number of successful byte reads |
| cursor | `Nat` | Offset of the next byte, initially at most length |
| carry | `Nat` or `Bool` | Typed state bound to the next iteration |

Its body directly calls `bounded_readonly` on those parameters, in order, and
a resolved transparent global step function. Aliases that resolve to the same
operation are harmless; another operation with the same spelling is refused.
Reordered arguments, inline closures, unsupported carry types, and arbitrary
recursive source bodies are outside this first reflector. The library's
semantic interface itself is polymorphic in the carry type.

A step receives `(needle, cursor, byte, carry)` and returns either
`Continue(next)` or `Break(result)`, with both payloads of the carry type. It
receives no buffer. The buffer and needle remain invariant across iterations;
cursor and remaining budget are loop-owned control state. No source argument
has a register assignment or calling convention here.

## Guard, reads, and exit precedence

At each iteration:

1. If `cursor >= length`, return `End(cursor, budget, carry)`.
2. Otherwise, if budget is zero, return `Exhausted(cursor, carry)`.
3. Otherwise read `base + cursor`. `None` returns
   `Denied(cursor, budget, carry)` without consuming a step.
4. `Some(byte)` grants that specific read. Invoke the body, advance cursor by
   one and consume one budget unit. `Continue(next)` repeats with `next`;
   `Break(result)` returns `Early(next_cursor, remaining_budget, result)`.

Consequently an empty input with zero budget ends normally; exhausting exactly
at the end returns `End`; a break on the final budget unit returns `Early`.
The early-exit cursor is the next unread position, so a search match is at its
predecessor. The total evaluator defines out-of-range starting cursors as end;
valid source/IR artifacts separately require `cursor <= length`.

`ReadonlyBytes.read` is an immutable function to `Option<BitVec(8)>`. Its
argument is the mathematical address, including base. `Some` is the caller's
read permission and value; `None` is denied access. The source tag identifies
the caller's byte source and is retained with the view. It is not an allocation
certificate, and giving two different functions the same tag does not prove
they refer to the same storage. A native memory relation must establish that
connection explicitly.

`ReadsByte` states an individual successful access. `LoopReadable` is defined
from the actual evaluator's outcome: denial is false, the other outcomes are
true. This makes access validity follow exactly the chosen path, without a
second recursive semantics. It requires neither bytes after early exit nor
any byte on an empty/exhausted path. It asserts only the reads within this
budget, not readability of the whole buffer.

`ReadonlyLoopArtifact` combines equality with a named source result, the initial
cursor bound, and these selected-path access premises. `loop_artifact_normal`
transports the access result to the actual source outcome. The generated source
agreement remains unconditional, so it also preserves denial behavior.

## Native representation obligations

The source counters are mathematical, not silently modular. `LoopWord` relates
a word at a supplied width to its `Nat` value, and `LoopAddressBound` requires
`base + length < 2^width`, so even one-past-end is representable. Together with the
cursor bound, this supplies a deliberately conservative nonwrapping contract.
The local advancement lemma connects a successful unsigned bound test to the
next cursor bound. Budget decrement occurs only in a `Succ(rest)` branch;
`loop_budget_predecessor` states its exact Nat result.

Native selection must prove word/Nat preservation for each update and discharge
these premises. A Nat carry also needs a representability invariant: for the
counting client, `initial_count + budget < 2^64` is a sufficient conservative
bound. This interface does not prove that arbitrary Nat step functions fit in
machine words, or claim an ABI encoding for the outcome constructors.

## Two clients and remaining boundary

`examples/function-ir/readonly-loops.hthr` supplies occurrence counting with a
Nat accumulator and first-match search with a Boolean result and early exit.
Their behavior is ordinary source code; there are no counting/search operations
in the loop model or reflector. Initializing search with `False` gives the
usual first-match interface. Application theorems about the count or earliest
index remain distinct from source agreement.

The native loop issue owns selection of the step bodies through shared regions,
guarded loads, placements, symbolic edges, counter invariants, and a complete
physical trace. In particular, it must not treat these semantic artifacts as
native certificates or introduce another source-loop evaluator. General memory
policy, writes, faults, and packing remain owned by the byte-memory issue.

## Shared body frontend checkpoint

The ordinary structured source reflector now recovers typed parameter lists
instead of assuming two 64-bit words. It admits `Bool` and literal bitvector
widths from zero through 64, Boolean matches, unsigned comparisons, constants,
modular arithmetic/bitwise operations, and passthrough results. Boolean values
use one-bit FunctionIR ports, with explicit conversion at the source boundary;
`Bool` and `BitVec(1)` remain different source types. Resolved type/operation
identities determine recognition, including Boolean constructor payloads.

The `byte_equal` helper used by both loop clients now reflects into the existing
`StructuredRegion`/`Node` representation and receives a kernel-checked source
expansion certificate. The certificate renderer folds that same IR and retains
DAG sharing. There is no additional predicate AST or loop-specific node family.

The complete `search_body` now follows this path too. Transparent monomorphic
helpers are reflected into shared regions, including their conditional
bodies and scalar argument computations. `Compose(prefix, continuation)` lets a
structured producer feed a later region while retaining inherited inputs by
port ID. Its validity requires continuation inputs to be available from the
prefix interface; its semantic contract composes both regions under the same
valuation. Helper expansion declines cycles or depth beyond 32 functions and
allocates fresh values only below ID 16384.

Since 2026-09-25 a helper may return a word as well as a Bool, and its
arguments may be helper calls in turn, so a chain `f(g(h(x)))` of branching
helpers compiles as nested compositions (a literal argument is substituted,
not passed in a register). The certificates cross each composition at the
helper call itself (`function_ir_cert::SourceValue`): the continuation is
certified over its own valuation and used at one that carries `{n}_source` =
`helper(args)`, and `{n}_link` checks the helper's body against the machine
code once. Checking a chain costs what its links cost; before, each level's
checks evaluated the whole chain beneath it
(`docs/native-first-program-design.md` §10.1).

Results from a nonrecursive two-constructor family with one common scalar type
parameter and one field per constructor use two ordinary result ports: payload,
then a one-bit discriminator. Nominal constructor identities are recovered at
the source boundary. This handles `LoopStep<Bool>` without a loop-specific IR
node and is also tested with an unrelated family carrying `BitVec(8)`. The
source renderer currently accepts one result from each composed prefix.

The unused Nat cursor has no machine port but remains universally quantified in
the source certificate. A consumed Nat is carried as a 64-bit word, its
modular image `word_of_nat(64, n)`, so `count_body` reflects too
(`docs/native-bounded-loops-design.md` §9a). The search certificate checks the
whole body against its actual source definition, including helper meaning;
stale helpers, swapped constructors, and changed payloads are rejected.

Physical composition and multiple result placement now use the same recursive
backend. `lower_structured_results` and `generate_structured_results` accept
explicit result-register maps. Composed prefixes may produce multiple values;
continuations receive these and inherited inputs by port ID. Both branch arms
use the requested result placements. Every result has a correctness theorem
and artifact over the same selected execution, bytes, memory frame, and exit
RIP. Inherited registers, including consumed selectors, remain protected.

Multi-result dataflow currently selects a dependency slice per result and
protects each finished result while selecting the next. This can recompute
shared nodes and decline avoidable register pressure; it does not invent
spills or edge-copy reconciliation. Signed comparisons below 64 bits still
decline: they need a signed normalization rule. Zero-extended placements
support widths 0–64 for constants, copies, bitwise AND/OR/XOR, unsigned
comparisons and (since 2026-09-30, `docs/native-tr-design.md` §4.1) add and
subtract, which are the word's operation masked to the width in a scratch
register (`BitVec::add_zero_extend_mask`).
Constants are reduced modulo their logical width before materialization;
comparison results remain normalized one-bit values. Generic bitvector
zero-extension laws justify the physical word operations, and placement/frame
proofs retain each value's actual width.

The complete reflected `search_body` now selects through these shared rules
and receives physical certificates for both payload and discriminator over
arbitrary normalized input placements. Its source expansion also checks
against the actual source definition, retaining the unused Nat cursor.
The `generate_elaborated_typed_x86` certificate API now connects these physical
results to the actual typed source call. It takes explicit input/output register
maps and emits one source-named `StructuredArtifact` per result over the same
execution. Public premises bind typed arguments to normalized registers; internal
valuations and graph witnesses are generated. Unused Nat arguments remain
universally quantified. For choice results, generated observers retain constructor
identity: the first constructor has discriminator False and the second True,
with a separately certified payload. Bool and BitVec(1) stay distinct source types.
The observation proofs use the shared Boolean-branch computation theorem.

The API emits certificates, not an OS calling-convention wrapper.

A successful physical read can now precede such a body through
`generate_elaborated_read_x86`. It selects a source `BitVec(8)` parameter and
an address register, then emits a canonical MOVZX byte load followed by the shared
body. The public contract replaces that parameter's entry placement with
`access.read(before.memory, address) = Some(byte)` and a low-canonical-address
premise. Other input placements are transported across the load automatically.
`ReadThenArtifact` joins that step to the existing `StructuredArtifact`, including
exact published bytes, memory preservation, total RIP advancement, and the
intersection of the load/body register frames. The body may return multiple
results; no application-specific machine semantics is involved.

This is the selected successful-read path. `None` cannot establish normal load
execution, and no read premise is imposed on paths outside this adapter. The
bounds/address composition below selects the actual guard and connects its read
address to the Nat cursor. A complete bounded-loop trace remains to implement.
Instruction fetch, fault handling, RET, and the host calling convention remain external.
The body checkpoint is not yet a compiled search loop.

The memory instruction subset is MOVZX r64, byte [base], without an index or
segment override. SIB bases and the zero-displacement Rbp/R13 forms are included;
canonical decoding is exact equality to these supported byte forms. See Intel's
[SDM, Volume 2B, MOVZX](https://cdrdv2-public.intel.com/868141/253667-089-sdm-vol-2b.pdf).
The optional byte-read interface is an explicit access grant, not a total memory
map or a full virtual-memory model.

The native export adapter keeps its two-`BitVec(64)`-input,
`BitVec(64)`-result restriction. Conditional Boolean helpers composed into such
functions now reach ordinary native export. Source expansion certificates
alone do not establish physical execution or a global `StructuredRegionHolds`
witness.


## Bounds-selected access composition

`AccessFragment` composes existing named `LoweredStructured` certificates with
byte loads, sequences, and branches. `structured` references a checked pure
leaf; `read` uses the same `ByteLoad` contract as the typed read adapter.
`branch` resolves its two forward labels from child byte lengths and declines
spans outside the signed short-branch range. `publish` emits the literal bytes,
`AccessCode`, encoding equality, and layout proof through structured emission.
It imports the modules containing the referenced pure certificates.

`ExecuteAccess` in `x86_64_access_code` is relational. A read carries a byte and
its `ByteLoadStep`; a sequence carries its intermediate state; a branch follows
the actual `structured_test(...).flags.zf` and `structured_branch_entry`.
Only the selected arm needs execution evidence. `access_read_then` consumes
existing `ReadThenArtifact` values, and the sequence/branch constructors compose
those proofs without repeating pure instruction semantics. `AccessArtifact`
packages execution, layout, and exact published bytes. It does not invent a
complete-loop result or ABI; typed child artifacts supply the observed results.
`access_memory` in the separately imported `x86_64_access_memory` module derives
memory preservation from execution itself.

`bitvec_nat` supplies width-generic, explicitly bounded addition and unsigned
comparison bridges. `function_ir_loop_x86` uses them to prove that the compiled
strict bounds test has the complement of `loop_run`'s end condition, that TEST/JZ
has the correct polarity, and that a selected ADD address denotes exactly
`buffer.base + cursor`. `loop_read_address` transports the Nat `ReadsByte`
premise through a caller-provided memory relation to the actual word operand.
Cursor advancement is representable on the selected in-bounds path. A wrapped
sum cannot satisfy these premises; low-canonical address evidence remains
explicit and separate from the mathematical nonwrapping bound.

The integrated tests select ordinary source functions for the guard, address
addition, identity/masked byte bodies, and the end result. Open-memory consumers
check successful-read and end-path artifacts. Native execution uses the exact
published bytes across 196,628 calls, including reads at the final accessible
page byte and denied pointers on end paths. Refusal controls cover wrapped sums,
signed/reversed bounds tests, swapped address operands, incorrect bytes, stale
branch displacements, and unsupported branch spans. This is one bounds/read transition. Budget selection,
carried-state updates, backward edges, outcome encoding, and bounded induction
remain under `native-bounded-loop-certificates`. Their design is
`docs/native-bounded-loops-design.md`, and `lib/native/function_ir/function_ir_loop_trace.hthr`
holds the bounded induction (`loop_trace`) over the `AccessLoop` code form.
