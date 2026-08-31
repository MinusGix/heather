# FunctionIR: typed regions, semantic graphs, and certified lowering

Status: **living design note, pre-implementation** (2026-08-30).

This document records the intended direction for the FunctionIR that replaces
the bootstrap constructor-tree IR in `lib/ir_v1.hthr`. It is deliberately not
a promise that the first implementation is permanent. The first version
should be good, but its more important job is to expose the next design
questions under real use.

Related boundaries are owned by:

- `docs/compile-typeclass-design.md`: source function to FunctionIR
  certificates;
- `docs/datarepr-design.md`: abstract values and runtime representations;
- `docs/x86-64-execution-boundary.md`: bytes, decoding, and typed x86
  execution; and
- `docs/certified-pass-algebra-probe.md`: compositional and
  relation-polymorphic pass certificates.

The current `Ir` remains useful bootstrap evidence. Its exact shape is not a
constraint on this design.

---

## 1. Direction

FunctionIR is a typed representation of one function body. It should be much
closer to typed SSA, growing toward an intuitively named RVSDG-like region
structure, than to the current constructor evaluator.

The likely larger architecture is:

```text
world/module IR
    owns definitions, functions, globals, imports, and linkage
        |
        v
FunctionIR
    describes one typed function body
        |
        | certified lowering, possibly factored through abstract proof IRs
        v
MachineFunction<Target> / typed target blocks
        |
        v
encoded bytes
```

Only some semantic layers need to be materialized as runtime compiler data.
Heather's proof system lets a correctness theorem factor a direct lowering
through arbitrarily many abstract languages, relations, algebras, or
existential witnesses without requiring the compiler to construct each one.

This distinction is fundamental:

1. **Persistent IRs** are objects the compiler actually constructs and
   transforms, such as FunctionIR and eventually a late target machine
   function.
2. **Abstract proof IRs** are syntax or semantic interfaces used to state
   reusable optimization and lowering theorems. They need not exist at
   runtime.
3. **Implementation views** are data structures used by algorithms, such as
   use-def indices, schedules, dominator trees, worklists, and interference
   graphs. They are not automatically new languages.

A concrete intermediate IR should justify itself through a transformation or
consumer that benefits from traversing it. Convenient proof factorization
alone does not require materialization.

## 2. Initial semantic scope

The first FunctionIR fragment should be deliberately small:

- typed function inputs and outputs;
- a pure acyclic region;
- explicit SSA/dataflow values;
- fixed-width bitvectors;
- constants if the first examples need them;
- `Add`; and
- region outputs, which serve as the initial return mechanism.

It should have no general effect structure yet. In particular, the initial
`Add` has no state input or output, cannot trap, and is deterministic. The
representation must nevertheless leave room for nested regions and explicit
effect dependencies later.

An initial function is conceptually:

```text
function add64(x: BitVec(64), y: BitVec(64)) -> BitVec(64) {
    z = Add(x, y)
    output z
}
```

### 2.1 Bitvectors and signedness

`Add` receives its meaning from its operand type:

```text
Add : BitVec(w) * BitVec(w) -> BitVec(w)
```

It is modular addition modulo `2^w`. There are no signed and unsigned integer
types: those are interpretations of bitvectors, not distinct storage values.
An operation names signedness only when the interpretation changes its
semantics, for example:

```text
LessThanSigned       LessThanUnsigned
DivideSigned         DivideUnsigned
ShiftRightArithmetic ShiftRightLogical
```

Alternative overflow behavior is likewise a distinct semantic operation,
such as checked, saturating, or carry-producing addition. Ordinary modular
addition remains simply `Add`. The internal operation may carry or infer a
width even when the surface/printed spelling does not mention it.

### 2.2 Floats are semantic types, register classes are not

Floating-point operations illustrate the representation boundary. A
FunctionIR float operation has floating-point semantics, including its format
and eventually the selected policy for rounding and exceptional values. Its
runtime representation may be the corresponding bitvector in an XMM register,
an integer register, a stack slot, several narrower locations, or software
state.

Thus register class and placement belong to lowering. They do not belong in
the identity of a FunctionIR value merely because x86 executes a float after
loading its bits into a special register class.

## 3. Operation families without prematurely building an IR framework

The graph/region machinery should be capable of being generic over an
operation family. Morally, such a family provides:

- types;
- operation kinds;
- input and output signatures;
- semantics; and, later,
- effect/control information needed by generic consumers.

The initial implementation should nevertheless expose one small official
core rather than attempt a general dialect ecosystem. Genericity in the
internal boundary is useful; immediately solving arbitrary dialect
composition, namespaces, parsing, versioning, cross-dialect canonicalization,
and a universal effect system is not.

Once a second real operation family exists, its pressures can determine how
much of this boundary deserves to become a user-facing IR framework. Building
such a framework is a potentially valuable direction, but it is not a
prerequisite for the first useful FunctionIR.

## 4. Regions and the RVSDG direction

The intended semantic unit is a region:

```text
Region:
    typed inputs
    operation nodes
    explicit dependency edges through values
    typed outputs
```

A node consumes values and produces one or more values. Multiple results
should be permitted by the representation even if the first `Add` produces
only one.

Later structured nodes may own nested regions with intuitive names such as:

- `Conditional`;
- `Loop`;
- `Function`/`Lambda`; and
- `Apply`/`Call`.

The design borrows the useful RVSDG idea—control and computation are
structured by regions and dependencies—without inheriting opaque Greek-letter
names or requiring the full node taxonomy initially. A loop may be a node
containing a cyclic semantic region while the enclosing region remains
acyclic.

## 5. Typing and validity: a hybrid representation

The IR should not make every compiler transformation perform deeply dependent
graph surgery. It should also not let malformed graphs enter semantic
theorems unchecked.

The current recommendation is a hybrid:

- nodes, value IDs, operand references, and declared types are ordinary data;
- operation signatures are explicit;
- a well-formedness judgment checks uniqueness, scope/dependency order,
  operation arity, input types, output types, and region boundaries;
- a validated FunctionIR packages or is indexed by that certificate; and
- semantic and optimization APIs normally consume only validated functions.

Typed views and lookup lemmas can recover strong local facts from a validated
function. This keeps compiler algorithms operationally simple while keeping
ill-typed IR outside the trusted semantic interface.

This is also a kernel-performance decision. A maximally intrinsic graph can
make equality, editing, deserialization, and transports expensive even when
its mathematical presentation is attractive. The hybrid boundary lets the
validator pay that cost once and lets transformations manipulate compact
data.

## 6. Sequence versus graph

There are two different questions hiding behind “is a region a sequence or a
graph?”:

1. Does node order have semantic meaning?
2. How are nodes stored, traversed, printed, and serialized?

For the pure FunctionIR region, the answer to the first should be **no beyond
dependencies**. The answer to the second may still be **a deterministic
topological sequence**.

### 6.1 Semantically unordered dependency graph

Benefits:

- It matches SSA and RVSDG dataflow directly: edges, not textual position,
  state why one node precedes another.
- Independent nodes are visibly independent and may be reordered,
  parallelized, or scheduled without changing meaning.
- Common-subexpression elimination, code motion, and graph replacement are
  naturally stated without proving that every irrelevant intervening list
  element is harmless.
- Graph denotation can make incidental schedules disappear from optimization
  correctness statements.
- Nested regions and explicit state edges extend the same dependency idea to
  structured control and effects.

Costs:

- Finite graphs do not provide the effortless structural induction of a
  syntax tree or definition list.
- Evaluation requires an acyclicity argument, a topological schedule, or a
  relational/fixed-point semantics.
- Reachability, freshness, graph isomorphism, and renaming become routine
  infrastructure.
- A raw node map has no natural deterministic printing or encoding order.
- Proving that all node equations determine unique results is more work than
  folding a well-scoped definition sequence.
- Graph mutation still has to preserve typing, ownership by regions, and
  absence of illicit cycles.

The unordered presentation removes incidental-order lemmas from client
theorems, but it does not remove proof work: much of it moves into generic
graph, scheduling, and well-foundedness infrastructure.

### 6.2 Semantically ordered definition sequence

Benefits:

- Validation and evaluation are simple left-to-right folds.
- Every operand may be required to refer to an input or an earlier result, so
  acyclicity and dominance are immediate from construction/validation.
- Structural induction follows the concrete representation.
- Construction, serialization, deterministic diagnostics, and debugging are
  straightforward.
- The order is already an executable schedule.

Costs:

- If order is semantic, independent definitions acquire a false dependency.
- Code motion and scheduling require permutation or weakening theorems.
- Proofs may become littered with “the relevant definition occurs somewhere
  before this use” facts.
- Positional or de Bruijn-like references cause index shifting under insertion
  and deletion.
- Syntactic equality distinguishes functions that differ only by the order of
  independent definitions.
- RVSDG's parallel/dataflow character is obscured if clients are encouraged to
  reason from list position.

Stable value IDs avoid the worst index-shifting costs, but they do not by
themselves make order semantically irrelevant.

### 6.3 Recommended hybrid: graph semantics, scheduled storage

The initial representation should store nodes in a deterministic topological
sequence, using stable value/node IDs rather than positional references. Its
well-formedness certificate proves that every dependency is available before
use.

The semantic abstraction should view that sequence as a presentation of a
dependency graph:

```text
stored region = graph nodes + one certified topological schedule
meaning       = dependency equations / region input-output behavior
```

Independent-node order is not intended to be observable. Initially the
evaluator may fold over the stored schedule because that is the smallest
executable definition. The important follow-up theorem is schedule
independence: any valid schedule for the same pure dependency graph has the
same region denotation.

This separates responsibilities cleanly:

- storage gets determinism and easy traversal;
- validation gets a cheap acyclicity/dominance check;
- execution gets a ready schedule;
- optimization correctness targets graph denotation rather than list
  accidents; and
- later instruction scheduling can replace the schedule without changing the
  graph's meaning.

An implementation may later split the representation explicitly into a node
map and a schedule list if random access or frequent rescheduling justifies
it. The first version need not pay for both structures.

This hybrid is particularly suitable for incremental RVSDG development.
Ordinary nodes inside a region form an acyclic graph. Structured control nodes
own subregions. Cycles are introduced through the semantics and interfaces of
`Loop`, rather than by admitting arbitrary backedges into every region and
turning all evaluation into fixed-point reasoning.

### 6.4 Proof consequences

Client proofs should not repeatedly establish that irrelevant definitions in
the stored sequence can be skipped. That fact belongs in generic
infrastructure:

- lookup and environment-extension lemmas for stable value IDs;
- weakening/frame lemmas for unrelated definitions;
- schedule-independence/permutation theorems;
- dependency-closed subgraph evaluation;
- renaming and fresh-ID invariance; and
- a bridge from sequential validation/evaluation to graph denotation.

Before schedule independence lands, the first implementation may state its
executable theorem over the canonical stored schedule. That is an
implementation milestone, not a declaration that sequence order is the
long-term meaning of a pure region.

## 7. Semantics and refinement

The common currency for compilation and optimization should be semantic
refinement/equivalence, not a required history of approved rewrite steps.

This supports two equally legitimate optimizer styles:

1. **Compositional verified rewrites.** A pass is built from local rules and
   generic traversal/composition theorems.
2. **Proof-producing or translation-validated optimization.** An optimizer
   computes by any useful method, then returns or invokes a certificate that
   its result refines the simpler source semantics.

The latter may use normalization, arithmetic reasoning, symbolic execution,
bitvector procedures, or a domain-specific checker. Its runtime algorithm
need not mirror the conceptual proof factorization.

The exact refinement relation remains open. The pure deterministic initial
fragment can begin with equality of input-output denotations. The relation
should be chosen so it can later express target nondeterminism, faults,
nontermination, and effect observations without reversing compilation
theorems or weakening them accidentally.

## 8. Abstract intermediate layers and rule composition

The first lowering need not materialize a WordIR. A theorem may factor:

```text
FunctionIR Add
    refines abstract fixed-width addition
    refines an x86 instruction pattern
```

“Abstract fixed-width addition” may be a relation, an algebra operation, a
proof-only syntax, or an existential witness. It becomes a concrete WordIR
only if a real shared transformation—such as width legalization, carry-chain
formation, or target-independent word simplification—benefits from traversing
it.

Instruction selection and register assignment are semantically distinct, but
they need not be separate initial passes. A selection theorem can quantify
over a location assignment:

```text
x      -> rx
y      -> ry
result -> rd
```

and select according to aliasing:

```text
rd = rx:               ADD rd, ry
rd = ry:               ADD rd, rx       // commutativity
otherwise:             MOV rd, rx
                       ADD rd, ry
```

Each rule should describe:

- required input placements;
- established output placements;
- aliasing/freshness conditions;
- register, flag, and memory clobbers;
- control-flow behavior; and
- a semantic refinement theorem.

Rules compose through those contracts. A first compiler may simply
instantiate the general rule with `RDI`, `RSI`, and `RAX`.

## 9. Materialization may be optimized away

Even an IR that is explicitly materialized in compiler source need not remain
a runtime allocation when Heather compiles its own compiler. Future compiler
optimization may fuse a producer and consumer, specialize generic lowering,
erase certificates, or replace a reified representation with a streaming
eliminator.

The design principle is:

> A lowering phase is characterized by its semantics and interface, not by a
> requirement that its complete output graph exist in memory.

Potential techniques include deforestation, staging, partial evaluation,
final encodings, proof erasure, and representation specialization. A useful
IR may therefore be reified for standalone tools, debugging, or transformations
that need random access, while disappearing from the optimized compiler path.

No such machinery is required for the first FunctionIR. The interfaces should
merely avoid making materialization semantically observable.

## 10. First vertical slice

The recommended first experiment is:

1. Define the minimal typed pure region containing `BitVec(64)` and `Add`.
2. Represent `add64` as two inputs, one node, and one region output.
3. Validate its stable IDs, dependencies, and operation typing.
4. Give it an executable/denotational semantics.
5. Prove a reusable, location-sensitive selection rule for x86 `MOV`/`ADD`.
6. Instantiate the rule with `RDI`, `RSI`, and `RAX`.
7. Add typed x86 block execution and concatenated canonical
   encoding/decoding.
8. Compose a theorem from FunctionIR behavior through decoded x86 execution:
   `RAX` contains the modular sum, memory and protected registers are framed,
   flags may be clobbered, and `RIP` advances by the encoded block length.

This is a placed pure leaf block, not yet a complete ABI function. It does not
claim stack, `CALL`, `RET`, fetch-from-memory, general allocation, branching,
or unbounded natural-number compilation.

The first slice should be handwritten enough to expose the right certificate
interfaces before generator design hides them.

## 11. Deliberate non-commitments and open questions

The design currently commits to direction, not final spelling. Open questions
include:

- the exact operation-family interface and how widths are inferred/stored;
- the concrete stable-ID and multi-result value-reference representation;
- whether stored node order begins as part of `Region` or as a separate
  certified schedule;
- the first graph-denotation and schedule-independence statement;
- whether validation certificates are stored, regenerated, or abstracted
  behind a checked wrapper;
- the direction and observation boundary of general semantic refinement;
- the eventual explicit state/effect dependency representation;
- the interfaces and intuitive names for conditional, loop, call, and
  function regions;
- when a late `MachineFunction<Target>` earns materialization;
- whether any abstract word layer develops a real transformation customer and
  should therefore become concrete;
- how location and clobber contracts scale to stack slots, calls, multiple
  register classes, and spills; and
- which reified compiler layers can later be fused away when compiling the
  compiler itself.

The implementation should record new pressure here rather than treating its
first convenient encoding as settled architecture.

## 12. Implementation log

### 2026-08-30: first pure region and x86 lowering slice

The first implementation lands in `lib/function_ir.hthr`:

- `Port`, the purpose-built `Ports` environment, stable Nat IDs, `Node::Add`,
  and `Region` are raw data; `Ports` owns lookup, freshness, uniqueness, and
  extension rather than exposing an arbitrary `List<Port>` as the region API;
- `RegionValid` checks unique inputs, typed/defined operands, fresh results,
  topological availability, and defined region outputs;
- `CheckedRegion` packages raw data with that certificate;
- `Valuation`, `NodeHolds`, and `RegionHolds` give the pure graph a relational
  equation semantics independent of environment-update order; and
- `add64_function` is the first checked region, with `add64_denotes` pinning
  its output to modular bitvector addition.

`lib/std/arch/x86_64/block.hthr` adds concatenated canonical bytes, placed
canonical decoding, functional normal block execution, and authoritative
relational block execution. `lib/function_ir_x86.hthr` selects
`MOV RAX,RDI; ADD RAX,RSI`, proves its six-byte canonical layout, decoding,
allowed relational execution, result refinement, memory and protected-GPR
frames, and RIP advance, and packages those facts into one placed-block
theorem.

The first generic theorem claiming that functional normal execution is
admitted by relational execution for every instruction list exhausted the
ordinary kernel fuel budget. The definitions themselves and the concrete
two-instruction certificate check. The generic theorem was therefore not made
part of the first API; `issues/x86-block-normal-execution-proof-fuel.md` owns
that proof-cost boundary. This is not a reason to specialize block semantics,
and no fuel increase is proposed.

The first validity literal exposed the former asymmetry between concise
conjunction types (`P ∧ Q`) and nested `And(...)` terms. The resolved
`issues/conjunction-introduction-syntax.md` added anonymous constructor syntax,
and `add64_valid` now writes its input-uniqueness tree as nested `⟨…, …⟩`.
Argument-slot sections do work for the two congruence functions in
`add64_denotes`; because slots are checking-only, the generic `cong_fn` carrier
arguments are made explicit to supply their expected function type.
