# FunctionIR: typed regions, semantic graphs, and certified lowering

Status: **living design and implementation record** (2026-08-31).

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

The first FunctionIR fragment is deliberately small:

- typed function inputs and outputs;
- a pure acyclic region;
- explicit SSA/dataflow values;
- fixed-width bitvectors;
- constants;
- modular `Add` and `Sub`;
- bitwise AND, OR, and XOR;
- immediate logical/arithmetic shifts;
- signed and unsigned less-than; and
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

### 2026-08-31: schedule independence and pressure-bearing lowering

The second slice adds `sum4`, a three-node graph with two independent additions
and a joining addition. Two topological schedules store the independent nodes
in opposite orders. Their `RegionHolds` propositions are equivalent by merely
reassociating and permuting conjunction evidence; `sum4_denotes` is shared by
both schedules through a node-local `add_node_denotes` rule. This is the first
concrete confirmation that stored node order is a schedule, not graph meaning.

The x86 selection uses four input registers, `RAX` for the left result, and
`R8` for the right result before joining them. This small amount of register
pressure exposed two useful certificate interfaces:

- `BlockArtifact` names the common execution, result, memory, RIP, and
  protected-register boundary instead of restating a deeply nested
  conjunction for every lowering; and
- `canonical_execute_block_cons` composes one canonical instruction with an
  already-certified tail without recursively normalizing an arbitrary list.

The five-instruction functional execution is deliberately expressed through
named stages. Asking `refl` to normalize the complete register state at once
exhausts ordinary kernel fuel; small destination and preservation facts compose
without raising fuel. This is evidence for generated local proof steps and
opaque stage boundaries, not for making the semantic graph sequential. The
current `sum4` regions are raw semantic examples; producing their
`RegionValid` certificates ergonomically remains a next validation/generator
slice.

### 2026-08-31: proof-carrying reference validation

`check_region_valid` now traverses raw regions and returns
`Option<RegionValid(region)>`. Successful lookup, freshness, uniqueness, node,
and output checks construct exactly the propositions used by `RegionValid`;
there is no Boolean mirror and therefore no separate soundness theorem.
`validate_region` packages successful evidence as a `CheckedRegion`, while
`CheckSucceeded` plus `proof_of_check_success` lets a closed declaration turn
the computed `Some` branch into an opaque named validity theorem. Both `sum4`
schedules are now ordinary checked regions, and rejection tests cover duplicate
IDs, undefined operands and outputs, and width mismatch.

The first reference checker returned a full decision `P ∨ ¬P`. That was the
wrong compiler boundary: rejected programs do not need recursively constructed
kernel refutations. Moving to `Option<P>` cut the cold validation probe from
roughly 33 seconds to 19 seconds; ensuring clients consume opaque validity
theorems rather than rerunning the checker reduced the focused cold fixture to
roughly 13 seconds. This is still too expensive for serious graphs, so
`issues/function-ir-validation-proof-cost.md` records the certifying-generator
target. The in-language checker remains the executable specification and a
useful dynamic fallback; it is not presumed to be the final fast path.

### 2026-08-31: untrusted direct certificate emission

The first certifying fast path lives on the compiler/tool side. Given the
concrete region model from which code is being emitted, it writes a
`RegionValid` theorem with direct `HasPort` constructor paths, reflexivity for
closed ID/width equalities, and order lemmas for distinct IDs. The generated
text is ordinary Heather source and the kernel checks it against the actual
region declaration. In particular, a test feeds the generator a stale model;
the resulting certificate is rejected by conversion. The generator therefore
improves proof construction without joining the trusted core.

This is deliberately not source reflection yet. The runtime compiler already
owns the concrete graph model, so duplicating that model into a decision
procedure would add work without adding trust. A later self-hosted compiler can
move the same analysis into the language while retaining the checked theorem as
the boundary.

Direct emission separates two costs that the reference checker had conflated.
It avoids recursively deciding known equalities, including unary-Nat width
literals, but it cannot make the current validity proposition compact. With
list-backed environments, every node carries freshness evidence against all
earlier ports and lookups carry linear constructor paths. The resulting proof
is quadratic even when generation is linear: the focused eight-node chain
checks, while probes at 20 and 100 nodes exceeded 60 and 90 seconds. The next
representation target is a compact validity environment that preserves stable
graph identities and schedule independence; see
`issues/function-ir-validity-environment-scaling.md`.

### 2026-08-31: compact directory/rank validity prototype

`RegionValidV2` now prototypes that compact environment alongside the original
relation. Its balanced directory maps stable IDs to a width and a unique
origin, either `InputAt(input_index)` or `NodeAt(node_rank)`. Bounds threaded
through the search tree prove global ID uniqueness in linear space. Exact
origins connect every raw input and node output to the directory, while operand
validity is directory membership plus the small condition that a producing
node's rank precedes its consumer. The directory cardinality excludes phantom
entries. Consequently, changing the schedule changes node ranks but does not
renumber stable IDs; both `sum4` schedules validate against the new relation.

The first balanced-tree emitter was still slow because it materialized the
entire transparent tree under one name. Every apparently logarithmic lookup
had to reconstruct that value before following its path. Emitting a persistent
tree of named subtree functions, an opaque ordering fact per subtree, and one
opaque lookup fact per stable port makes the operational cost match the data
structure. Generic composition lemmas keep the generator untrusted: they only
assemble ordinary kernel-checked `DirectoryWithin`, membership, availability,
and indexed-list evidence.

A second sharing boundary is equally important. A single nested proof of one
hundred scheduled nodes spent 68.9 seconds in frontend elaboration even after
directory lookup was cheap. The generator now emits named node-list suffixes
and an opaque `NodesIndexed` stage for each suffix. At 20 nodes this reduced the
final record assembly from 15.7 seconds to 0.087 seconds. The focused 100-node
test, including FunctionIR module setup, then completed in 13.66 seconds; the
old list-environment certificate had not completed in 90 seconds. A stale V2
model is rejected against the real raw region, confirming that none of these
sharing declarations is a trusted shortcut.

This section records the prototype stage. The direct replacement described
below removed the temporary `V2` distinction rather than converting compact
certificates back into the quadratic proposition.

### 2026-08-31: compact validity becomes the only boundary

The experiment is now the implementation. `RegionValid` is the balanced
stable-ID directory plus schedule-rank relation, and `CheckedRegion` packages
that relation directly. The old list-environment validity proposition,
recursive `check_region_valid`, computed-validation wrappers, and quadratic
Rust emitter were deleted. There is no compatibility theorem or fallback path
that reconstructs their proof trees.

The compact emitter now owns the plain `generate` name. Add64 and both sum4
schedules retain public validity theorems and checked-region constructors in
`lib/function_ir_certificates.hthr`. That module is generated from the same
untrusted concrete models used by the compiler path; a focused golden test
regenerates it on request and otherwise detects drift. Consumers import the
certificate module only when they need packaged validity, while
`function_ir.hthr` holds the IR, compact validity vocabulary, semantics, and
raw examples.

The cutover keeps malformed-model rejection on the host side and stale-model
rejection at the elaborator/kernel boundary. It also keeps the 100-node chain,
mixed-width sparse DAG, semantic schedule-equivalence, and x86 refinement
rails. The performance debts found while building it remain separate language
issues: frontend sharing of large proof composition, named-argument expected
types, and run-aware reduction of very large closed Nat order comparisons.

## 13. Executable DAG lowering

The first executable, proof-producing x86 lowering now closes
[[function-ir-x86-lowering-generator]]. It is a vertical compiler slice:
given a concrete pure 64-bit Add DAG and input placements, the untrusted host
tool computes use counts, selects `MOV`/`ADD`, assigns and reuses spill-free
temporaries, and renders an ordinary Heather certificate. The kernel checks
the plan against both the actual `RegionHolds` graph and x86 execution.

Proofs are staged at instruction granularity. Each emitted instruction has a
small result fact over an abstract machine state, and live values cross it
with concrete-register frame facts. `ValuePlaced` composition then connects
those local machine facts to successive graph equations. This is not merely a
presentation detail: whole-node reflexivity crossed the kernel fuel rail on
sum4, whereas local facts keep normalization bounded and expose the intended
compiler invariant directly.

The generated module replaces the handwritten add64 and sum4 bodies. A golden
drift test ties the checked file to the renderer; one semantic backstop checks
that complete generated module without redundantly elaborating an identical
dynamic copy. The alternate sum4 schedule is generated into an independent
test module, preserving end-to-end coverage while letting its kernel check run
in parallel with the primary module. Host tests cover deterministic selection,
last-use reuse, a long constant-pressure chain, precise pressure decline, and
stale-model rejection at conversion.

The initial boundary deliberately began small: `Add` at width 64, one result,
declared input/temporary locations, and no spills. The internal plan separates
selected instructions, placements, liveness, and emitted proofs enough for new
operation families and a later spill policy.

The first ALU expansion confirms that boundary. FunctionIR now denotes
constants, modular subtraction, bitwise operations, immediate shifts, and
signed/unsigned comparisons at arbitrary widths. The executable x86 subset
handles the five 64-bit register-register binary operations Add/Sub/AND/OR/XOR
through the same allocator and placement rule. A mixed graph keeps two
subexpressions live, selects seven instructions, and checks through canonical
encoding, decoded execution, and final FunctionIR refinement. Constants,
shifts, and comparisons remain separate backend work because they introduce
variable-length immediate encodings, count normalization, and flag-to-value
materialization rather than another instance of the destructive RR rule.

Generated refinement scaling now uses three explicit sharing boundaries. A
compact context prevents every local theorem from restoring the complete graph
and input-placement telescope; opaque node-list suffixes make each semantic
equation a constant-depth projection; and immutable input registers are framed
directly from the entry state rather than copied through every instruction.
Instruction execution is likewise staged over persistent suffixes because the
tempting generic induction theorem currently exceeds kernel fuel. Together
these changes move a 20-node mixed ALU artifact from beyond five minutes to
64.5 seconds and keep a 50-node probe linear at 154.1 seconds. The remaining
cost is approximately one opaque execution stage per instruction and one
placement stage per node, not growth in graph depth or live-input distance.

## 14. Next implementation path

The ALU core, first structured conditional, linked join, and first source
frontend are now present. The planned sequence is therefore:

1. [[source-function-ir-expression-dags]] grows source reflection from one
   binary operation to expression DAGs and constants. This converts useful
   20--100 node source functions without changing the semantic boundary.
2. [[function-ir-recursive-structured-lowering]] replaces the current single
   comparison-prefix/conditional normal form with recursive structured
   selection and composition.
3. [[function-ir-x86-shift-legalization]] finishes the remaining ALU family,
   while [[function-ir-x86-fused-compare-branch]] can remove comparison
   materialization when measured worthwhile.

Three language-performance issues remain deliberately off this critical path:
[[frontend-large-proof-composition-cost]],
[[named-argument-checking-context-loss]], and
[[nat-order-large-run-comparison]]. Generated staging and ordinary-size IDs
make current work viable; these should return to the foreground when measured
as blockers or when parallel work can improve them without distorting compiler
architecture.

### 2026-09-01: first structured conditional and machine join

FunctionIR now separates the flat scheduled dataflow DAG from recursive
control structure. `StructuredRegion` has a `Dataflow` leaf and a directly
recursive `Conditional` carrying explicit outer inputs, a one-bit condition,
the arguments visible to either branch, a common yielded interface, and two
nested regions. Direct recursion is intentional: the tempting
`List<NodeF<Region>>` encoding is nested recursion, which Heather correctly
rejects today. Keeping `Region` as the leaf also preserves its useful
schedule-independent graph semantics rather than replacing it with a tree.

Validity forbids hidden captures, requires the condition to be an available
one-bit port, checks unique interfaces, requires both branch input interfaces
to equal the declared arguments, requires both yield interfaces to agree, and
recursively validates each branch. Denotation inspects the condition and asks
only the selected branch to hold. Branch-local stable IDs may consequently be
reused: the two branch environments never coexist semantically.

The first executable lowering accepts two dataflow leaves with a single
64-bit result. It independently selects and assigns each leaf from the common
argument placement, materializes a `ConditionalBlock` whose choice is read
from the low bit of a real GPR, executes exactly the chosen certified leaf,
and joins both results in the requested output register. A placement theorem
connects the zero-extended FunctionIR bit to the machine selector, so the
compiler cannot prove the convenient branch rather than the branch the
machine observes. The checked acceptance function chooses `Add` or `Sub` and
joins in `RAX`.

The abstract `ConditionalBlock` remains the semantic composition boundary.
The first linker-facing slice now also emits one concrete byte sequence around
it: canonical prefix, `TEST r64,r64`, `JZ rel8`, true leaf, `JMP rel8`, and the
false leaf. `JZ` and `JMP` have exact two-byte encodings, an executable strict
decoder, signed displacement execution, and negative controls for empty,
truncated, trailing, and unknown-opcode inputs. The generated example is 35
bytes; its checked layout computes forward displacements +8 and +6 from the
canonical leaf lengths and rejects distances beyond signed rel8.

Decode and canonical deterministic control execution are checked for the
whole linked object. The linked path changes flags and RIP before entering a
leaf, whereas the abstract conditional enters that leaf directly. Generated
ALU blocks now carry composable `GprOnlyStep` certificates: each supported
instruction proves with a tiny local fact that its GPR result depends only on
incoming GPRs, and the generator chains those facts over the scheduled block.
TEST and short control preserve the GPR file, so both linked leaves agree with
their abstract counterparts. A Boolean observation theorem then relates the
real TEST/JZ choice to the FunctionIR bit and composes the concrete linked
result with the existing structured refinement.

The effect certificate deliberately lives in `function_ir_x86_support`, not
the base x86 model: moving a generic instruction case split into the base made
the x86 rail grow from roughly 29 to 90 seconds, while generated per-step facts
restore the base cost and leave the 35-byte linked certificate essentially
unchanged.

Physical join correctness is now checked as well. Layout endpoints advance by
the encoded block byte length, `LinkedConditionalLayout` carries exact semantic
targets in addition to the auditable rel8 distance facts, and generated named
facts connect the executed prefix and leaves to those endpoints. Tiny pure
Boolean/RIP lemmas select the taken or untaken result, so the emitted
`*_linked_reaches_join` theorem proves both executions finish at the same
`linked_join_start` without placing the entire x86 machine in a dependent match
motive. This keeps physical layout out of semantic region validity while
preserving the abstract refinement as the reference specification.

The first producer-to-control composition adds `Sequence(prefix,
continuation)`. Its flat prefix extends the continuation's scope with the
union of the prefix's original inputs and declared outputs. This is more useful
than requiring every live input to be repeated as a prefix result, while still
preventing the continuation from capturing an undeclared intermediate node.
Denotation is simply the prefix `RegionHolds` paired with the continuation's
structured denotation.

The executable acceptance artifact uses an `UnsignedLessThan` prefix. It
materializes the comparison in `RDX` with zero/`CMP`/`SETB`, carries the
protected `RDI` and `RSI` placements through that block, then uses the produced
bit to choose Add or Sub and joins the result in `RAX`. Machine execution
packages the prefix's final state as an explicit existential witness before
conditional execution, ruling out both skipping the producer and branching
from the entry state. The generated refinement consumes `graph.left` for the
comparison and `graph.right` for the selected continuation.

The generator intentionally supports this first normal form rather than
pretending to be a recursive structured backend already: one one-bit prefix
result, inherited branch arguments, two dataflow leaves, and one 64-bit join
result. General recursive selection is tracked by
[[function-ir-recursive-structured-lowering]].

### 2026-09-01: first source function reaches a checked x86 artifact

`function_ir_source` now recognizes an explicit initial source fragment: a
monomorphic two-argument `BitVec(64)` function whose body is one
`bitvec::add`, `sub`, `band`, `bor`, or `bxor` call over its parameters. It
constructs the corresponding stable-ID region directly, emits compact
`RegionValid`, invokes the existing x86 selector, and proves the graph result
equal to the actual source function application. A final `BlockArtifact`
observes that source application as its result, so the path is source function
to canonical bytes and relational machine execution without passing through
`ir_v1`.

The initial entry point reads a surface declaration, but the compiler-shaped
path now reflects the checked global body. It resolves operation heads by
their absolute global identities, peels the elaborated lambdas, and retains
the source function's canonical qualified name for certificates checked in a
different module. Generated source imports that defining module explicitly.
The kernel still rejects a stale graph; reflection does not bypass ordinary
elaboration or checking.

Nested Add/Sub/AND/OR/XOR and closed `bitvec::ofNat(64, literal)` expressions
lower by deterministic postorder traversal. Structural memoization recovers
sharing after elaboration: even when a surface `let` has substituted and
duplicated its body, equal elaborated subterms receive one stable FunctionIR
port. Unsupported resolved globals decline at this boundary with the admitted
operation family named.

Source denotation is staged like machine execution. Generated suffix facts
extract each `NodeHolds` equation at constant projection depth, and one opaque
value theorem per node composes that equation with its operands' earlier value
facts. A small named semantic function per node keeps those value facts from
reprinting the complete source subtree. Separate opaque expansion equalities
then relate each named semantic value to the corresponding elaborated source
expression one operation at a time. Operation-specific 64-bit congruence
lemmas and fully explicit local endpoints are intentional: recursive generic
congruence calls lose endpoint inference, while dependent indexed witnesses
cross kernel fuel after only a few layers.

The scaling rail now builds real elaborated source functions containing all
five binary ALU operations and constants, then measures source elaboration,
reflection, FunctionIR emission, x86 emission, parsing, frontend work, kernel
work, and per-declaration categories separately. Host work is negligible even
at 100 nodes: source elaboration is 71ms, reflection 1ms, both generators about
144ms, and parsing 31--36ms. The checked proof boundary is the cost:

- the 20-node source frontend checks in 20.9s;
- the 100-node source frontend checks in 199.3s;
- the complete 20-node source-to-x86 artifact checks in 105.6s; and
- the complete 100-node artifact checks in 677.7s, split almost evenly between
  kernel (337.0s) and frontend (340.7s).

At 100 nodes, execution stages cost 187.9s, value placement 155.9s, source
value facts 98.4s, and global/boundary declarations 169.6s; the latter includes
76.7s in `gprs_congruent`. Source graph staging costs 23.5s and the final source
artifact only 17.5s. Thus no hidden Rust compiler or parser bottleneck remains:
the next performance work is generated-proof elaboration/checking. Explicit
expanded endpoints also make the source certificate 7.46MB despite bounded
per-declaration proofs; [[generated-source-semantic-term-sharing]] tracks a
shared/direct elaboration representation for that remaining duplication.
[[source-function-ir-expression-dags]] remains open only for the focused stale
internal-edge control and performance follow-up.

Proof source emission now uses the Rust-side construction API documented in
`docs/generated-heather-emission-api.md`. Expressions, positional and named
calls, projections, equalities, lists, lambdas, parameters, statements,
blocks, declarations, and modules are explicit values with deterministic
rendering. The new source compiler constructs its complete denotation and
artifact proofs through this API, and the common straight-line x86 header has
also migrated. An explicit raw-expression escape hatch supports gradual
migration without making arbitrary strings the default representation.

Rendering remains an untrusted final sink. The resulting source takes the
ordinary parser, elaborator, and kernel path, retaining name resolution,
implicit insertion, diagnostics, and an inspectable certificate. A future
direct elaborator-data sink can target the same construction IR if profiling
shows parsing is material; [[generated-heather-direct-elaboration]] records
the measurement and equivalence requirements rather than prematurely making
compiler generators construct kernel terms.

### 2026-09-02: block arguments and a shared continuation

The next control-flow core now models the fact that the earlier conditional
only approximated: a machine join is not merely two arms agreeing to write the
same global value ID.  Predecessor edges pass typed values and a successor
binds fresh SSA parameters.  `BlockArgument(width, value, parameter)` records
that transfer, and its semantics equates the successor parameter with the
selected predecessor value at the shared width.

The first concrete `ControlRegion` is the useful four-block diamond rather
than an unrestricted CFG: a straight-line producer, two selected dataflow
arms, and one shared continuation.  Both edges must pass exactly their arm's
declared outputs, must bind the same ordered parameter interface, and the
continuation must accept precisely that interface.  Parameters are unique and
fresh from the values visible before the branch.  This is genuine SSA block
argument semantics while retaining structurally obvious acyclicity and an
RVSDG-like region boundary.

`ControlRegion` is temporarily separate from the older `StructuredRegion`.
Adding a large constructor to the already-hot recursive type made two warm
x86 model probes grow from the earlier focused baseline to roughly 73 seconds,
even after the constructor's non-recursive conjunction was factored.  A
record-shaped first core avoids widening every existing eliminator.  This is
a migration boundary, not a legacy promise: the block-argument route should
replace the old conditional once its certified backend subsumes it.

The Rust-side interpreter executes this representation independently of x86.
It evaluates the selected arm, snapshots all edge sources, binds successor
parameters with parallel-copy semantics, and executes the continuation once.
The first acceptance graph is `max_plus(a, b, c)`: unsigned compare `a < b`,
pass either `b` or `a` as fresh parameter `selected`, carry `c` as a second
parameter, and compute `selected + c` in the join.  Controls cover both arms,
equality, modular overflow, and stale edge interfaces.

The initial x86 selector produces the corresponding physical block view.  It
materializes the comparison in `RCX`, maps the selected value from `RSI` or
`RDI` into the common join register `R8`, carries `c` in `RDX`, and lowers the
single shared continuation to `MOV RAX,R8; ADD RAX,RDX`.  Edge copies are
planned as parallel transfers and cycles currently decline explicitly rather
than silently emitting a sequentially wrong copy.  The remaining certification
step is tracked by [[function-ir-control-region-x86-certification]].
