# Elaborator modularity

`crates/elab/src/lib.rs` grew around a valid invariant: elaboration is one
transaction over a shared global environment, and many features genuinely
interact. The way out is therefore not to pretend the features are independent.
It is to make the shared state explicit, separate pure mechanics from policy,
and give each effect a narrow owner.

## Direction

The target is a small orchestration layer with four kinds of component:

1. **Session state** owns committed declarations, name tables, instances,
   generated definitions, and the kernel gate. It changes only at declaration
   commit boundaries.
2. **Declaration state** owns goals, warnings, speculative mismatch notes,
   recursion guards, fuel, and restart bookkeeping. It is created for one
   declaration and either committed or discarded.
3. **Local context** owns Γ plus the parallel surface information required to
   elaborate under binders.
4. **Mechanisms** implement checking/inference, application and unification,
   matching, receiver/operator dispatch, and declaration lowering. A mechanism
   receives the smallest combination of the three state views it needs.

This keeps the useful property of a single elaboration transaction without
making every method a peer on one enormous `Elaborator`.

## Seams established first

The initial mechanical split deliberately kept several files included in the
crate root. That preserved Rust privacy and name resolution exactly while
making the dependency seams visible:

- `diagnostics.rs`: public diagnostic data;
- `context.rs`: Γ and surface bindings, now an ordinary module that owns their
  parallelism and prefix operation;
- `recursion.rs`: structural-recursion guards and convoy state;
- `surface.rs`: surface traversals and argument-slot lowering, now an ordinary
  state-free module;
- `unification.rs`: implicit-application scratch state and the structural
  unifier, now an ordinary state-free module.

The remaining included files should become ordinary modules only after their
inputs have been made explicit. Doing that first would replace one giant
implicit API with hundreds of `pub(crate)` fields and methods, which is
movement rather than modularity. `context.rs`, `surface.rs`, and
`unification.rs` have crossed that threshold. The context module owns one
coherent state vector, while the other two import their complete inputs
explicitly and cannot reach elaborator state.

## Extraction progress

### 1. Declaration transaction

The first phase is now present: `DeclAttempt` owns goal allocation and
capacity, mismatch notes, operator fallback records, slot probing, and motive
speculation. Its `prepare`, `clear_goals`, and `finish` operations encode
the retry/cleanup lifecycle in one place. Warnings remain an output accumulator
across declarations, and pending derived instances remain item-level because
inductive and representation declarations use them too.

The second phase is also present. `check_decl` now returns an inert
`PendingDecl`; `commit_decl` is the only operation that installs its Ψ
binding or updates the global, name, member, and stored-surface registries.
The ordinary path is consequently:

1. create an attempt;
2. elaborate into a proposed binding;
3. solve goals and run the kernel gate;
4. commit the binding and attempt emissions.

For an ordinary declaration, rollback is now structural: no fallible operation
occurs after committed state starts changing.

## Session registries

### Source-language registries

Group the lookup-only state by invariant, not merely by feature:

- `Names`: scopes, declarations, globals, and member/constructor lookup;
- `Types`: inductives, tags, forded skeletons, and generated definitions;
- `Traits`: classes, instances, designations, and derived dictionaries;
- `Representations`: data representations, implementations, obligations,
  access aliases, and provenance.

`Names` is now established in `names.rs`. It owns current, stored, and
temporarily overridden module scopes; the ambiguity index; callable globals;
the member-name fast path; and stored surface declarations. Ordinary globals
enter all of those indexes through one `commit_global` operation. Its reverse
Ψ lookup is explicit, so reflection no longer scans a hash map to recover a
callee name.

`Types` is now established in `types.rs`. It owns inductives by qualified name
and nominal tag, constructor lookup, the forded-skeleton fingerprint, the
record-field fast path, tag allocation, and generated definitions. All
fallible inductive checks finish before `Types::commit` installs those views;
a failed declaration neither consumes a tag nor partially enters a type
index.

`Traits` is now established in `traits.rs`. It owns classes and the class-member
fast path, instances, operator designations, and canonical derived
dictionaries. Declaration and resolution code use explicit registration and
lookup operations; every query that crosses a hash-backed table returns a
canonical order before terms or diagnostics can observe it. Lexical instance
scope and pending derivations intentionally stay outside the registry: they are
temporary state belonging to the current elaboration attempt, not committed
trait declarations.

`Representations` is now established in `representations.rs`. It owns reprs by
spec identity and written name, parameterized monomorph names,
implementations and their provenance, the declaration-ordered obligation
ledger, and designed/generated access mappings. A repr or implementation
enters its linked lookup and reporting views through one commit operation.
Access mappings must exist provisionally while generated source and obligation
diagnostics are checked. Representation declarations therefore run inside the
session transaction described below; failed reprs and implementations cannot
leak those provisional names or any ordinary declaration emitted before the
failure.
Generated-source nesting and the active `derive()` route remain outside: both
are transient control flow for the declaration being elaborated, not committed
representation metadata.

`MetaPrograms` is now established in `metaprograms.rs`. It owns elaborator-held
meta definitions and the optional elaboration slot each template claims. It
answers qualified definition lookup, collision ownership, and slot dispatch;
callers cannot reach either backing map. Signature and name validation finish
before one infallible commit installs the definition and slot views together,
so a slot can never point at a missing definition. `meta_pushed` remains on the
elaborator because it is dynamic oracle scope during a meta declaration, not a
committed meta program.

All five source-language registries are now explicit. No caller iterates one
of their hash-backed tables to emit terms or diagnostics.

## State that intentionally remains on `Elaborator`

Not every remaining field is a missing registry:

- `psi`, `delta_psi`, and the optional kernel gate are the declaration
  transaction's trust boundary and belong to the orchestration layer;
- `attempt`, `instance_scope`, `pending_derived`, warnings, generated-source
  depth, the active derive provenance, resolution depth, and fuel describe the
  item or call currently being elaborated;
- `meta_pushed` is dynamic scope while checking a meta program;
- `result_only_memo` is a performance cache whose removal changes no result.

This inventory is a constraint on later views: committed state, dynamic scope,
configuration, and caches should not be bundled merely because one mechanism
reads several of them.

## Remaining sequence

### Established: generated bundle transaction

A representation generator emits several ordinary declarations. Each one uses
the normal check/commit path, so `session.rs` now gives the orchestration layer
one `SessionCheckpoint` spanning Ψ, its δ view, names, types, traits, meta
programs, and representations. Representation and implementation declarations,
plus the public generated-source entry point used by mutation controls, all run
through the same transaction. An error restores that snapshot and clears the
Ψ-indexed result-only memo, whose absolute indices may otherwise be reused by
later declarations.

Dynamic scope, diagnostics, configuration, and attempt scratch deliberately
remain outside the checkpoint. Their existing owners delimit those lifetimes;
the transaction means “committed program facts are atomic,” not “rewind the
entire elaborator object.” Regressions cover both an arbitrary generated bundle
crossing Ψ/name/type registries and a representation implementation whose early
generated declarations precede a later kernel failure.

### Established: meta-program registry

`MetaPrograms` owns definition and slot lookup behind one registration
operation. Unit tests pin the ordinary-definition and claimed-slot cases, while
the registration suite proves a rejected second claimant neither displaces nor
damages the original dispatcher.

### 1. Bidirectional core

The first supporting seams are established. Surface rewriting and structural
unification are ordinary modules rather than textually included fragments.
Their privacy boundary makes accidental access to `Elaborator` impossible, and
focused unit tests exercise both mechanisms without constructing one.

Local context is now an ordinary `context` module as well. It owns Γ together
with the parallel binder names and callable skeletons, and its tests pin both
the push invariant and the distinction between positional binder state and
dynamic scope preserved by a prefix.

`application.rs` owns callable skeleton metadata and the first vertical
bidirectional mechanism: explicit application down a Π spine. That engine sees
only the local context and two capabilities—weak-head normalization and
argument checking—through `ExplicitArgElab`. A unit test supplies both with a
tiny fake, proving that the application loop itself needs neither an
`Elaborator` nor a session fixture. The current `Elaborator` implements those
capabilities as a transition point; the eventual `ExprElab` can implement the
same interface without changing application policy.

Implicit application now crosses the same boundary in two pieces.
`ImplicitPlan` fixes the Π schedule and the scratch-world size without session
state, including the reserved slots for checking-only arguments.
`retry_obligations` owns solver-before-argument ordering, readiness, fallback,
and fixpoint termination. Dictionary search, deferred expression elaboration,
unification, and declaration-goal promotion enter only through
`ImplicitApplicationElab`; the `Elaborator` implementation is the transition
adapter. A fake implementation tests both the plan and the obligation queue
without constructing an elaboration session.

The remaining `apply_implicit` body still constructs and discharges the
scratch world in `lib.rs`. Its next split is to move that Π walk into
`application.rs` once argument inference/checking and expected-type harvesting
are expressed as capabilities. Promotion and trait resolution should remain
services at that boundary, not fields on a generic context bag.

Move `elab_ty`, `elab_check*`, and `elab_infer*` behind an `ExprElab`
view borrowing the immutable session and mutable declaration attempt. Split
application, match lowering, and member/operator dispatch into collaborators
only when their parameter lists describe real dependencies.

The desired test is architectural: pure unification and surface rewriting can
be unit-tested without constructing an `Elaborator`; expression elaboration
can be tested with a small session fixture; declaration tests continue to
exercise commit and rollback end to end.

`ExprElab` is ready only when all of these are true:

- it names its session, attempt, local-context, and dynamic-scope inputs
  individually rather than holding `&Elaborator`;
- constructing it does not clone committed state;
- it cannot commit a declaration or mutate a global registry;
- application, matching, and dispatch can be moved one at a time without
  widening the view for unrelated callers.

The size of `lib.rs` is evidence, not the success criterion. A smaller file
that hides the same dependency graph behind `ExprElab { elab: &Elaborator }`
would be less honest than the large file we have now.

## Lessons from the registry pass

- Move ownership and enforce invariants before changing algorithms.
- A fast-path index belongs with the canonical table it summarizes.
- Hash-backed queries that affect output must sort at the registry boundary.
- Temporary lexical or generated-source modes are not committed metadata.
- When provisional registry state is required during checking, snapshot the
  committed session and test the failure path explicitly.
- Ordinary Rust modules became useful only after the dependency boundary was
  real; privacy changes were then a consequence rather than the objective.

## Guardrails

- Preserve the kernel as the sole trust boundary.
- Preserve byte-for-byte deterministic terms and diagnostic ordering.
- Prefer moves and state grouping before algorithm rewrites.
- Keep each intermediate commit behavior-preserving and run the full
  `heather-elab` suite.
- Roll back every affected registry when one generated source declaration
  fails; do not call a feature transactional when only its primary table rolls
  back.
- Do not create a generic “context” or “services” bag. If a component still
  needs all of `Elaborator`, the boundary is not ready.
