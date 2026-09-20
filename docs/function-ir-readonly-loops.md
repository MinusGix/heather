# Bounded read-only loop contract

The source/IR contract lives in `lib/function_ir_loop.hthr`. It is a semantic
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
Boolean helpers are reflected into shared regions, including their conditional
bodies and scalar argument computations. `Compose(prefix, continuation)` lets a
structured producer feed a later region while retaining inherited inputs by
port ID. Its validity requires continuation inputs to be available from the
prefix interface; its semantic contract composes both regions under the same
valuation. Helper expansion declines cycles or depth beyond 32 functions and
allocates fresh values only below ID 16384.

Results from a nonrecursive two-constructor family with one common scalar type
parameter and one field per constructor use two ordinary result ports: payload,
then a one-bit discriminator. Nominal constructor identities are recovered at
the source boundary. This handles `LoopStep<Bool>` without a loop-specific IR
node and is also tested with an unrelated family carrying `BitVec(8)`. The
source renderer currently accepts one result from each composed prefix.

The unused Nat cursor has no machine port but remains universally quantified in
the source certificate. Consuming a Nat still requires a representation proof;
`count_body` therefore remains unsupported. The search certificate checks the
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
spills or edge-copy reconciliation. Existing leaf restrictions still apply:
64-bit arithmetic and comparisons with normalized one-bit comparison results.
Byte operations and Boolean dataflow inputs/constants still need selection support,
followed by guarded reads and complete bounded-loop traces. Thus `search_body`
has a checked source expansion but does not yet have a physical certificate.

The native export adapter keeps its two-`BitVec(64)`-input,
`BitVec(64)`-result restriction. Conditional Boolean helpers composed into such
functions now reach ordinary native export. Source expansion certificates
alone do not establish physical execution or a global `StructuredRegionHolds`
witness.
