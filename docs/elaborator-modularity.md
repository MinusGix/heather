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

Implicit application is now a complete vertical slice as well.
`ImplicitPlan` fixes the Π schedule and scratch-world size without session
state, including reserved slots for checking-only arguments. The implicit
engine owns scratch construction, meta numbering, the Π walk, deferred
arguments, spill-based and expected-type learning, obligation fixpoints,
promotion orchestration, diagnostics, global discharge, and explicit
overapplication. Dictionary search and declaration-goal promotion remain
services rather than fields on a generic context bag.

`ImplicitApplicationElab` names the semantic operations the mechanism cannot
own: argument classification, inference and checking, unification harvests,
expected-type harvests, dictionary resolution, goal promotion, and the
trait-specific blocked-goal diagnostic. `Elaborator` implements that interface
as a transition adapter. Fake implementations exercise the schedule, retry
queue, and complete scratch-world lifecycle without constructing an
elaboration session. No `Elaborator::apply_implicit` forwarding method remains.

The declaration goal arena is established too. `goals.rs` owns the reserved Ψ
prefix, stable source identities, implicit-promotion capacity discovery,
allocation and naming, freezing, speculative marks and rollback, discharge
state, diagnostic reports, the real goal world, and the final substitution.
`DeclAttempt` holds that owner rather than seven parallel goal fields, and
consumers can observe only its stable base or ask it to perform a lifecycle
operation. In particular, all expression probes now roll back both goal
records and source keys through one operation; the old operator-carrier probe
only truncated records and could leave a stale key behind.

Goal solving remains orchestration on `Elaborator` because checking an `on`
right-hand side and comparing a statement still need expression elaboration
and the kernel oracle. The arena supplies cloned goal obligations and accepts
solutions without exposing storage. When `ExprElab` is introduced, its goal
effect should be the arena's allocation capability, not `DeclAttempt`.

The kernel oracle seam is established. `SemanticOracle` owns one completed
global world and its fuel policy, and is the only ordinary stage-1 path that
assembles transparent reduction or conversion calls. (The certificate
interpreter retains its specialized cached evaluator.) Its constructors make
the three worlds explicit: committed Ψ, the cached δ-padded expression world
plus dynamic meta binders, and the goal arena's real statement world. It
offers transparent and deliberately opaque WHNF, conversion, and bounded
reduct streams; indexed, forded, quotation, resolution, goal, and expression
consumers no longer pass `delta_psi`, dynamic binders, and `fuel` separately.

Diagnostic reading is a distinct capability with a distinct contract.
`DiagnosticOracle` can only expose an `El`-headed type within a caller-owned
step budget, returning `None` for a stuck term or exhaustion. `display.rs` now
owns that decoder/speller/fallback sequence. Semantic reduction reports
exhaustion to elaboration; diagnostic decoding silently degrades; surface
spelling performs no reduction. Kernel typing remains direct at the gate and
at explicit proposal checks—it is judgment, not normalization, and folding it
into this oracle would erase a useful boundary.

The first staged `ExprElab` view is now established in `expr.rs`. It owns a
semantic oracle value and borrows two declaration-local capabilities: a
goal-allocation-only view and the argument-slot probe cell. Local Γ is passed
to the operations that need it. It holds no `&Elaborator`, session registry,
commit operation, or arena lifecycle access. Constructing the view only clones
the oracle's shared world handle unless dynamic meta scope actually requires a
completed world.

The first migrated slice is intentionally made of leaves: closed type forms,
literal/universe/hole/slot inference, hole/slot checking, and the semantic
half of expression WHNF. The next slice moves primitive structural type
formation—vectors, `Fin`, dependent functions, and equality. Those forms see
only a small `StructuralTypeElab` collaborator: recursive type lowering, named
type lowering, and term inference/checking. Binder extension stays local to
the mechanism, including callable skeletons and universe-bound type variables.
Named types now cross one explicit read-only policy operation; the rejected
type-splice form is local and needs no collaborator at all.

Unit fixtures construct the view directly, infer a numeral, allocate a goal,
and exercise structural type formation with a tiny fake collaborator, all
without an `Elaborator` or session. The root still owns the registry-sensitive
`unspell_here` pre-pass before type WHNF; that spelling policy is not smuggled
into the semantic capability.

Inference has begun crossing the same boundary. Type syntax used as a term
(`a = b` and explicit type literals) lowers through the existing type
collaborator and is coded inside `ExprElab`; the context-free refusal for an
inferred vector literal lives there too. The expression-to-type shape reader
is now a state-free surface operation shared by this path, motives, universe
checking, and type-subject lookup rather than a helper hidden in `lib.rs`.

Equality-specific checking has crossed as well. `refl` and auto-refl receive
two semantic decisions by name: registry-aware reading of the expected type,
and conversion in the real goal-statement world. Auto-refl allocates its
fallback through the existing goal-only capability. Root orchestration keeps
the `refl` shadowing decision, so the view owns equality construction without
gaining name resolution. The obsolete general `new_goal` forwarding method is
gone; only keyed implicit promotion still reaches the arena from the root.

Checking-only indexed constructors are the next complete slice. Vector
literals and `FZ`/`FS` now preserve their folded `Vec`/`Fin` shapes and reduce
only the indices inside `ExprElab`; their sole outward operation is recursive
checking of an element or predecessor. Root orchestration still decides
whether `FZ` or `FS` is shadowed by a local or declaration constructor. This
keeps name resolution out of the view while removing both term constructors
and their reduction policy from the root elaborator.

Core numeral checking follows the same boundary. `ExprElab` owns the direct
`Nat` term and the canonical folded `Fin` index, including successor peeling;
the root's remaining numeral helper is explicitly the overloaded
`Numeral<T>` class path. Thus structural syntax no longer reaches class
registries, and class resolution no longer obscures the built-in semantics.

The remaining canonical leaf, `trivial`, also lives in the view. Expected-type
reading is now a shared capability composed by equality and Unit checking;
goal-world conversion and diagnostic spelling remain separate extensions.
Root resolution retains the local/declaration shadowing guard, so moving the
term construction does not move name policy with it.

Lambda checking has now crossed the first non-leaf boundary. `ExprElab` owns
the function-spine traversal, binder/skeleton alignment, context extension,
universe-binder registration, and `Term::Lam` construction. The root exposes
only expected-type reading and display, recursive checking, annotation
lowering, and domain conversion. In particular, no callback manipulates the
local context and the view still has no registry or declaration authority.

Every remaining root checking arm crosses a subsystem boundary: blocks
elaborate statements and mutate attempt scope; quotes change layers; matches
own motive synthesis, rollback, and recursive guards; constructors and
dot/application perform registry dispatch; universe checking combines
type-former lookup with speculative type reading.

Lambda inference has followed checking across the boundary without merging
their bidirectional rules. Both modes share one context-extension mechanism,
including callable skeletons and universe-bound type variables. Inference
still requires annotations, synthesizes the Π spine, and takes a named mode:
ordinary inference refuses implicit binders whose marks would be lost, while
`LetSkeletonHarvest` admits them precisely because the statement elaborator
records the written skeleton on the alias. The root now supplies recursive
body inference and shared annotation lowering; it no longer traverses or
constructs either kind of lambda.

The last canonical inference names have moved with it. After root decides
that `FZ` or `trivial` is not shadowed by a local or declaration constructor,
the existing ExprElab classifier owns `FZ`'s checking-only refusal and
`trivial`'s fixed `Unit^0` synthesis. All remaining inference arms now cross a
real subsystem boundary rather than merely constructing a core term.

Only expression-as-type remains in the root `elab_ty` match. It combines
operator rewriting, indexed-family recognition, value-parameter formation,
term inference, and universe decoding; moving it behind one callback would
only rename the old coupling. Continue moving `elab_check*` and `elab_infer*`
behind `ExprElab` where their inputs become narrow named queries, and return to
expression-as-type after those underlying policies have their own seams. Split
application, match lowering, and member/operator dispatch into collaborators
only when their parameter lists describe real dependencies.

The desired test is architectural: pure unification and surface rewriting can
be unit-tested without constructing an `Elaborator`; expression elaboration
can be tested with a small session fixture; declaration tests continue to
exercise commit and rollback end to end.

The staged view satisfies the initial boundary when all of these remain true:

- it names semantic, declaration-effect, local-context, and dynamic-scope
  inputs individually rather than holding `&Elaborator`;
- constructing it does not deep-clone committed state;
- it cannot commit a declaration or mutate a global registry;
- application, matching, and dispatch can be moved one at a time without
  widening the view for unrelated callers.

The size of `lib.rs` is evidence, not the success criterion. A smaller file
that hides the same dependency graph behind `ExprElab { elab: &Elaborator }`
would be less honest than the large file we have now.

### Sequence after application

The remaining routes are not equally ready. Take them in dependency order:

1. **Continue `ExprElab` in stages.** Choose the next checking/inference family
   by capability shape, then add named read-only session queries one policy at
   a time. Keep local context per-call and declaration effects narrower than
   their owners; the view must never store `&Elaborator` or gain commit
   authority.
2. **Match elaboration.** Move convoy, motive, recursive-guard, Nat/Fin, and
   indexed/forded matching only after `ExprElab` exists. Its speculative goal
   rollback and binder-sensitive lowering make this a high-risk consumer, not
   a good place to discover the view.
3. **Dispatch last.** Named arguments, member lookup, class dispatch, indexed
   dictionaries, operator carriers, designations, and compatibility fallback
   are several policies, not one `dispatch.rs`. Split pure argument
   normalization first, then carrier/callable queries, operator policy, dot
   resolution, and dictionary construction.

Moving lambda helpers merely to reduce line count is intentionally not a
roadmap item. Move them when their binder, skeleton, and conversion policies
have explicit expression capabilities; otherwise the result is only widened
privacy and forwarding methods.

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
