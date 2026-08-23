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

The initial mechanical split deliberately keeps several files included in the
crate root. That preserves Rust privacy and name resolution exactly while
making the dependency seams visible:

- `diagnostics.rs`: public diagnostic data;
- `context.rs`: Γ and surface bindings;
- `recursion.rs`: structural-recursion guards and convoy state;
- `surface.rs`: surface traversals and argument-slot lowering;
- `unification.rs`: implicit-application scratch state and the structural
  unifier.

The included files should become ordinary modules only after their inputs have
been made explicit. Doing that first would replace one giant implicit API with
hundreds of `pub(crate)` fields and methods, which is movement rather than
modularity.

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

Rollback is now structural: no fallible operation occurs after committed state
starts changing.

## Next extractions

### 1. Global registries

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

`Representations` remains. It should expose deterministic lookup and explicit
commit methods. No caller should iterate a hash-backed registry to emit terms
or diagnostics.

### 2. Bidirectional core

Move `elab_ty`, `elab_check*`, and `elab_infer*` behind an `ExprElab`
view borrowing the immutable session and mutable declaration attempt. Split
application, match lowering, and member/operator dispatch into collaborators
only when their parameter lists describe real dependencies.

The desired test is architectural: pure unification and surface rewriting can
be unit-tested without constructing an `Elaborator`; expression elaboration
can be tested with a small session fixture; declaration tests continue to
exercise commit and rollback end to end.

## Guardrails

- Preserve the kernel as the sole trust boundary.
- Preserve byte-for-byte deterministic terms and diagnostic ordering.
- Prefer moves and state grouping before algorithm rewrites.
- Keep each intermediate commit behavior-preserving and run the full
  `heather-elab` suite.
- Do not create a generic “context” or “services” bag. If a component still
  needs all of `Elaborator`, the boundary is not ready.
