# Native compiler architecture review

Review date: 2026-09-20. Implementation examined: `4db435c`.
The inventory below describes that commit. Following the review, the user
authorized removal of the specialized buffer profiles. Calculator expansion
is paused. Recursive source reflection, selection, physical certificates, and
assembly export now implement the first bounded checkpoint; broader multi-result
interfaces remain in the first issue. The bounded read-only source/IR contract
now has a shared evaluator, typed carry/exit interface, and generated source
agreement for counting and search. It is documented in
[the loop contract](function-ir-readonly-loops.md); body selection and physical
loop certificates remain the next step. The inventory remains historical.
Integration acceptance is tracked in
[the shared-lowering milestone](../issues/native-shared-lowering-milestone.md).

## Recommendation

Generalize the existing FunctionIR/native certificate composition boundary
before adding new buffer functionality. Use a nested pure conditional to
validate the boundary first, then two independent bounded buffer loops.
The prototype is available in Git history rather than as active infrastructure.

The problem is distributed special cases across selection, layout, and proof
construction. Merely moving the same templates into tactics or into Heather
would preserve those special cases. Conversely, reusable semantics and small
composition theorems are useful library code even when all applications of
those theorems are generated.

## Cleanup decision

Removed `--buffer-cursor` and `--buffer-scan`, their dedicated Rust generators,
five scanner/cursor model modules, two acceptance targets, recognition/decimal/
space-counting examples and host drivers, and both build guides. Removed the
valuation-parameter extension whose only callers were those profiles.

Retained FunctionIR/source arithmetic, structured conditional semantics and
lowering, reusable callee contracts, live-value sharing, checked simultaneous
stack saves, byte-certificate helpers, bundled-model sealing, and test-isolation
fixes. The showcase parser library and calculators are unchanged.

No scanner-specific model is being preserved under a new generic name. Recover
individual facts from `git show 4db435c:<path>` if a future shared interface
needs them. Old scanner issues are retired as removed/superseded, without
claiming their unfinished proofs were completed.

## Inventory at 4db435c

| Path | Evidence in the implementation | Current boundary |
| --- | --- | --- |
| Bootstrap certgen | [certgen.rs](../crates/elab/src/certgen.rs), [certgen_cert.hthr](../lib/certgen/certgen_cert.hthr) | Reflection, in-language transcription and a first-order certificate fold; Rust reads back and renders checked declarations. It targets the constructor-based `ir_v1` model, with a restricted recursive source shape. It is an automation precedent, not an existing x86 loop backend. |
| Source to FunctionIR | [function_ir_source.rs](../crates/elab/src/function_ir_source.rs), `reflect_elaborated`, `generate_elaborated_x86` | Resolved elaborated operation identities and arithmetic expression DAGs; the main arithmetic reflector requires two parameters. Native call composition has additional reflection entry points. This is not yet general source reflection for nested control and loops. |
| Structured FunctionIR | [function_ir_cert.rs](../crates/elab/src/function_ir_cert.rs), [function_ir.hthr](../lib/native/function_ir/function_ir.hthr) | Recursive `Dataflow`, `Sequence`, `Conditional` semantics and validation exist. These variants do not include a loop or buffer read. |
| Structured x86 lowering | [function_ir_x86_lower.rs](../crates/elab/src/function_ir_x86_lower.rs) | `lower_conditional` requires dataflow leaves. `generate_prefixed_conditional` handles a restricted comparison prefix and one word result. `lower_control_region` handles a diamond with edge transfers and a shared continuation, but currently refuses nonempty arm computations. Recursive semantics therefore exceed backend coverage. |
| Calls and saved values | [calls.rs](../crates/cli/src/native/calls.rs), [composition.rs](../crates/cli/src/native/calls/composition.rs), [callable.rs](../crates/cli/src/native/calls/callable.rs) | Reusable callee contracts, live-value selection, checked save slots, and symbolic call placement exist. Their placement/frame interfaces are specialized to this path. They provide useful ingredients, not a general allocator or machine-function linker. |
| Buffer profiles | `crates/cli/src/native/buffer.rs`, `crates/cli/src/native/scan.rs` (removed; see 4db435c) | Reuse arithmetic compilation, then surround it with dedicated templates. The scanner has its own surface `Word`/`Tree` walker, `ScanCode`, fixed register convention, offsets, and proof emission. Its source-equality certificate checks the reflected result, but that does not make this a shared frontend. |
| Proof rendering | [heather_emit.rs](../crates/elab/src/heather_emit.rs) | Structured declarations, parameters, expressions, and blocks already exist. The control-region emitter adopted them; the newer scanner again emits whole declarations through `Module::raw(format!(...))`. |

The removed scanner certified body/source agreement, body frames, refinement
of a pure bounded model, byte equality, and guarded machine entry. It did not
certify a complete repeated machine execution. The retired
[loop-refinement issue](../issues/x86-buffer-scan-loop-refinement.md) records
that gap; removal does not turn it into a completed proof.

## Where the abstractions are leaking

1. **Control structure is represented more than once.** FunctionIR already
   describes nested branches, while scanner lowering builds a separate branch
   tree. Completing recursive structured lowering would remove a reason for
   applications to grow their own branch compiler.
2. **Machine interfaces are implicit in templates.** The scanner fixes live
   values to R8–R11/RSI and bodies to a small scratch set. Calls use a separate
   clobber/placement scheme. A compositional selector needs explicit input and
   output placements and checked preservation facts at each boundary.
3. **Layout reasoning is coupled to an application.** Scanner offsets such as
   29, 38, 57, and 62 appear in layout and certificate construction. The calls
   path already resolves symbolic function references, but does not provide
   arbitrary conditional/backward label references. Extract only the local
   fragment/label support needed by the next client.
4. **Proof construction repeats routine bookkeeping.** Frames, intermediate
   states, branch spans, and byte chunks should follow the selected machine
   structure. Large symbolic execution expressions are a poor fallback: the
   existing controls have already exposed conversion-fuel failures.

These findings support extending shared interfaces. They do not establish that
all proof cost comes from templates, nor that moving a fold into Heather will
make checking faster. No performance measurements were made for this review.

## Proposed responsibility split

| Responsibility | Handwritten foundation | Generated for each compilation |
| --- | --- | --- |
| Source meaning | FunctionIR semantics and source reflection schemas | Validity and agreement with the actual elaborated source |
| Instructions and memory | Instruction semantics, explicit access premises, local effect laws | Selected instruction witnesses and required access obligations |
| Placement and preservation | Rules for moves, frames, joins, and call contracts | Port/register mappings, checked edge transfers, preservation applications |
| Control and layout | Sequence/conditional/bounded-loop composition and relative-address lemmas | Label resolution witnesses, intermediate states, branch and exit composition |
| Application behavior | Specification and any nontrivial semantic invariant | Applications of applicable arithmetic/induction automation |

Selection should return a description of the chosen blocks plus their value
interfaces, effects, and symbolic control edges. Certificate construction
should fold that description into small named proofs. Host metadata such as a
claimed write set is a proposal: the emitted proof must check it against the
actual instructions. Byte equality, source agreement, and execution composition
remain separate obligations that the final artifact connects.

This is an interface proposal, not a requirement to introduce several complete
new persistent IRs. Start by extending the existing lowering result structures
and `heather_emit` APIs. The first-order certificate representation in bootstrap
certgen is a useful pattern; translating native compilation through `ir_v1`
would conflict with the documented FunctionIR direction.

A deterministic certificate fold is the first tool for predictable compiler
obligations. Focused tactics may discharge residual bitvector, equality, or
arithmetic goals. Automatic discovery of arbitrary loop invariants is not a
prerequisite. A bounded loop with explicit carried values gives the compiler
an induction schema relating source iterations to machine iterations; proving
that the result counts occurrences is a separate application theorem.

## Small validation sequence

### 1. Prove reuse before adding memory or loops

Use ordinary source functions with nested unsigned conditionals and arithmetic,
first nesting in one arm, then the other, and retaining a live value across a
branch. Extend elaborated source reflection and recursive structured lowering
together far enough for these cases. A constructed IR-only test is useful but
does not satisfy the source-to-code milestone.

Reuse existing arithmetic, frame, and linked-branch lemmas. Introduce explicit
placement interfaces where recursive composition requires them. Fixed common
result placements and honest register-pressure refusals are acceptable first;
general spills and parallel-copy cycle breaking are separately owned work.

Success: the same recursive selection/proof routine handles both source
shapes, emits a complete physical conditional artifact, and requires no
example-specific register or RIP theorem. Reject wrong bindings, clobbers,
branch destinations, and stale source at local proof boundaries.

Owner: [recursive structured lowering](../issues/function-ir-recursive-structured-lowering.md).
Broader reconciliation: [join placement](../issues/function-ir-x86-join-placement.md).

### 2. Add the smallest reusable buffer/loop contract

Specify read-only byte access over supplied storage, with explicit base,
length, cursor, readable-address premises, and memory preservation. Keep the
access behind the selected guard in the execution certificate. Revisit the
prototype guarded-load facts in Git history where their assumptions fit. Do not require an
allocator, writable memory, or a full effect system first.

Choose and document one bounded source recursion/iteration fragment and its
FunctionIR representation. Carry cursor, accumulator, and remaining budget
explicitly. State the word/Nat relation and prevent decrement underflow; a
machine fuel register alone is not a termination proof. Keep source budget
exhaustion observable and distinct from end-of-input. This source/IR loop
contract is still a design gap, not an implemented capability.

Extend symbolic local layout only enough for the selected forward and backward
edges. Connect the complete execution, result, memory frame, and common exit
to the source loop and emitted bytes. Host I/O, ABI adapter, RET, and fetch
boundaries must remain explicitly scoped wherever still external.

Relevant owners: [byte memory](../issues/byte-memory-access-model.md),
[symbolic layout](../issues/x86-symbolic-fragment-layout.md), the new
[source/IR loop contract](../issues/function-ir-bounded-readonly-loop.md), and
[native loop certificates](../issues/native-bounded-loop-certificates.md).
Settle the source/IR contract before implementing native loop machinery.

### 3. Test two independent loop clients

First client: count occurrences of a runtime-selected byte in the entire
bounded input. Unlike the removed `count_spaces`, mismatches continue scanning.
Second client: locate the first selected byte, with early success and an
explicit not-found outcome. Together they vary carried results and exits.

Both use caller-owned input and scalar results. Input and needle vary after
compilation; the host only supplies storage and I/O. No heap allocation, AST,
parser combinators, decimal overflow, or Unicode representation is needed.

The second client must use the same source/IR/selection/certificate path with
no new application-specific machine model, register/RIP lemma family, or native
profile template. User-facing routine machine proofs are not acceptable as the
price of adding that second client. Application specifications can differ.

Validation includes empty input, all byte values, runtime needles, nonzero
cursors, exact bounds, early exit, limit exhaustion, guard pages, open-memory
proofs, and corrupted certificates under existing resource limits.

## Ordered implementation issues

1. [Recursive structured lowering](../issues/function-ir-recursive-structured-lowering.md):
   the next bounded slice includes ordinary source reflection and nested pure
   conditionals with a live value across a branch.
2. [Bounded read-only source/IR loops](../issues/function-ir-bounded-readonly-loop.md):
   choose loop-carried interfaces, read dependencies, and exhaustion semantics.
3. [Native bounded-loop certificates](../issues/native-bounded-loop-certificates.md):
   extend shared selection and automatically compose complete execution proofs.
4. [Two-client integration](../issues/native-shared-lowering-milestone.md):
   occurrence counting followed by first-match search through the same path.

Calculator-specific expansion and decimal Nat refinement are outside this
queue. Prefer structured emission for new declarations; a full emitter rewrite,
general tactics framework, linker, or allocator is not a prerequisite for the
first nested-conditional slice.

The buffer clients test the resulting architecture. Reconsider calculator
features only after that test demonstrates shared compiler capabilities.
