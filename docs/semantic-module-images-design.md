# Semantic module images

Status: accepted design, stages 1 and 2a complete; Stage 2b underway. Owner:
`issues/semantic-module-images.md`.

## 1. Problem and target

Heather's declaration cache remembers that a finished kernel declaration was
accepted. A hit still parses the source, resolves every name, elaborates every
surface declaration, runs the elaborator's conversion and weak-head oracles,
reconstructs generated definitions and every frontend registry, walks and
hashes the resulting kernel syntax, and only then skips the final kernel gate.

That was the right first cache when the final gate dominated whole-file time.
It is no longer sufficient. The standard arithmetic closure used by Omega has
573 declarations and takes about 173 seconds both with 570 fresh kernel checks
and with 573 cache hits. Five Omega acceptance binaries now account for more
than half of the full suite's reported target CPU time, mostly by rebuilding
the same semantic prefix.

The target is an incremental compilation boundary:

1. an unchanged imported module is installed from its already-elaborated
   semantic image without parsing or surface elaboration;
2. a changed suffix elaborates against exactly the world the ordinary source
   path would have produced;
3. the first persistent implementation does not trust the image for theorem
   soundness; imported kernel bindings are rechecked before metadata is made
   visible;
4. theorem proof changes do not invalidate consumers when their statements
   are unchanged; and
5. the same representation supports CLI checks, a resident daemon, tests,
   parallel module scheduling, and eventually Heather's compiler.

This design does not claim to make a newly changed theorem cheap. It removes
unchanged dependency work. Kernel and elaborator optimization for the changed
root remain independent, measured work.

## 2. The semantic world

An `Elaborator` mixes two different lifetimes today.

Committed program state:

- kernel context `psi` and its delta-unfolding view `delta_psi`;
- module scopes, globals, surface signatures, and name indexes;
- nominal types, constructors, tags, and generated definitions;
- classes, instances, designations, and derived dictionaries;
- representations, implementations, obligations, and access paths;
- assumption provenance; and
- checked meta-program definitions and slot registrations.

Transient session state:

- the current declaration attempt and instance scope;
- generated-source and implementation-provenance modes;
- pending derived instances;
- warnings and Omega success/failure reports;
- pushed meta binders and resolution depth;
- conversion memos and metrics;
- lint profile, fuel, and the installed kernel gate.

A semantic image contains the first list and none of the second. This is the
same boundary already used by `SessionCheckpoint` for transactional rollback;
the first stage makes it an explicit, testable value instead of keeping it an
implementation detail of the failure path.

Configuration is supplied by the session which forks or installs an image.
Diagnostics belong only to work performed by that session. A cache oracle is
never inherited implicitly: installing one is an explicit trust decision by
the caller.

## 3. Two image forms

### 3.1 In-memory semantic prefix

`SemanticImage` is an opaque, clonable snapshot of all committed state. A new
elaborator fork starts with fresh transient state and an isolated copy-on-write
semantic suffix.

This stage establishes completeness and isolation. It is immediately useful
to resident processes and speculative sessions, but it does not cross a
process boundary and therefore does not by itself solve repeated Cargo test
binaries or fresh CLI invocations.

### 3.2 Persistent module delta

A disk image stores the semantic delta contributed by one module, not a dump
of the whole `Elaborator`. Its logical payload is:

- kernel bindings appended by the module, in commit order;
- module scope and name/index additions;
- additions to every nominal, trait, representation, provenance, generated-
  definition, and meta-program registry; and
- enough checked surface schema to support the features which deliberately
  re-lower a declaration at an instantiation site.

Scratch fields have no encoding because they are not semantic facts. Module
deltas compose in loader dependency order to produce the same accumulated
world as the source path.

The first format may require the exact ordered dependency-interface vector.
That makes absolute global positions stable and avoids a premature relocation
format. A later format may encode global references by interface hash and
relink them into the current telescope; the existing Merkle identity already
defines the position-independent name for that work.

## 4. Identity and invalidation

An image header contains:

- an image-format version;
- an elaborator-semantics fingerprint covering the image schema and frontend
  code which constructs its metadata;
- the existing kernel-semantics fingerprint;
- the exact source digest;
- the ordered dependency interface hashes;
- the module's resulting interface hash; and
- every checking option that can change elaborated output or acceptance.

The source digest selects a reusable elaboration result. The resulting
interface hash controls downstream invalidation. These are deliberately
different identities: editing a theorem proof changes its source/image but,
because theorem bodies are opaque downstream, does not change the theorem's
interface or invalidate consumers.

Definitions include their bodies in their interfaces because conversion may
delta-unfold them. Inductive and registry-producing declarations include the
semantic declarations and generated definitions that consumers observe.

No identity is based on an allocation address. Pointer identity may accelerate
one in-process operation but never changes image bytes or cache identity.

## 5. Trust boundary

The initial persistent loader treats disk bytes as untrusted acceleration
data.

1. Decode with bounds and reject malformed or unsupported images.
2. Match all header identities before using the payload.
3. Starting from the already-accepted dependency world, recheck every stored
   kernel binding in order at its declared layer.
4. Keep frontend metadata quarantined until every binding succeeds.
5. Atomically commit the validated delta.

Frontend metadata can influence which term later elaboration constructs, but
that term still faces the ordinary kernel gate. Corrupt metadata can cause a
diagnostic, rejection, or tool failure; it cannot establish a false theorem.
Structural cross-checks between metadata and kernel bindings remain desirable
for robustness and determinism, not as the root theorem-soundness argument.

This deliberately leaves performance on the table if imported kernel checks
become expensive again. The existing trust ladder remains available:

- recheck from the stored term;
- replay recorded kernel search decisions;
- trust a content-addressed local verdict for an inner-loop quick mode; and
- run a fresh or replay-verified final build.

The safe recheck rung lands first. Omega's equal cold/warm measurements say it
can still remove the dominant cost.

## 6. In-memory representation

The eventual committed world is immutable and shared. An elaboration session
has an immutable base plus a small mutable overlay for the module or
transaction it is building. Successful module completion freezes the overlay;
failure drops it.

A simple parent-linked map for every lookup risks making resolution linear in
import depth. Acceptable implementation shapes are immutable base tables plus
one current overlay, or lazily flattened indexes cached by world identity.
Persistent data structures are justified only if measurement shows that the
base-plus-overlay shape is insufficient.

`GlobalCtx` already shares its binding vector, but copy-on-write appends copy
the vector when a fork first commits. The registry tables are less persistent:
several derived `Clone`s copy maps, strings, vectors, provenance paths, and
stored surface AST. Stage 2 moves these behind the same explicit committed-
world boundary rather than relying on the accidental cost of `derive(Clone)`.

The first Stage 2 slice uses two-level copy-on-write. A `SemanticImage` and
all of its forks share one `CommittedWorld`; detaching that small world copies
only handles, because each durable registry is independently shared. The first
write to a particular registry then detaches just that registry. Temporary
stored-syntax resolution scopes live on the elaboration session, not in the
shared `Names` registry.

This is an ownership implementation of the base/overlay boundary. Stage 2b's
first conversion makes `Names` a sequence of immutable module-sized layers
plus one mutable current-module delta. Image capture seals that delta by
sharing it and starts restored suffixes empty; name resolution streams across
the layers without constructing a flattened candidate table. Re-entering one
module keeps one layer, so lookup depth follows the module closure rather than
REPL/source-chunk count.

Ψ now uses persistent, bounded chunks. Full 64-binding chunks are sealed and
shared; a snapshot shares its at-most-63-binding tail, so a subsequent append
copies at most that bounded tail. Absolute lookup remains O(1) by quotient and
remainder into fixed-width chunks. This also bounds the
cost of the ordinary `psi`/`delta_psi` sharing after each declaration—the flat
vector could recopy a growing suffix repeatedly, not merely once at image
restore. Exact/debug rendering deliberately exposes only the logical binding
sequence, never chunk boundaries, because that rendering participates in
elaboration and cache identity.

The remaining registries still detach as whole tables on first mutation.
Later Stage 2b slices apply the measured layering shape where table size
warrants it; measurements must continue to distinguish O(1) image/fork
creation, lookup depth, and first-write detachment.

## 7. Loader and compiler architecture

The CLI loader resolves the module DAG and, for each node:

1. computes source and ordered dependency identities;
2. loads and validates a matching image when present;
3. otherwise elaborates source normally and freezes the successful delta;
4. publishes the resulting interface hash; and
5. continues with dependents.

Independent ready nodes may later compile in parallel against immutable
dependency worlds. Within-module parallel declaration checking is separate and
requires an explicit dependency/name prepass; it is not part of this design's
first implementation.

A resident daemon retains accepted semantic worlds in memory. Editor, agent,
and command sessions become isolated suffixes over a pinned prefix image. A
kernel or elaborator fingerprint change restarts the resident world rather
than attempting live migration.

## 8. Meta execution and compilation

Module images remove repeated meta-program elaboration, but a newly invoked
meta program may still execute through the general evaluator. Checked
elaboration-time programs may eventually compile to bytecode or native code:
their output is an ordinary generated kernel term and is checked normally, so
the accelerator need not join the theorem-soundness core.

This distinction is important for Heather-in-Heather. The kernel evaluator
used for conversion stays conservative and trusted. Generators, analyzers,
Omega reconstruction, and compiler passes may be aggressively accelerated
above it because their products remain proof-carrying.

## 9. Staging

### Stage 1 — explicit committed image

- Promote the transaction checkpoint's complete committed state into opaque
  `SemanticImage`.
- Fork an elaborator with fresh transient state and caller-controlled policy.
- Prove isolated suffixes and exact downstream equivalence against a fresh
  source closure.

This stage defines the boundary. It does not claim a cross-process speedup.

### Stage 2 — immutable base and module overlay

- Move committed state behind an explicitly shared world.
- Accumulate new module facts in an overlay and freeze atomically.
- Measure snapshot, first suffix commit, and lookup costs as the world grows.

Stage 2a is complete: explicit shared world, independently shared registries,
session-local resolution scopes, atomic pointer rollback, and behavioral plus
ownership tests. Stage 2b has converted the name registry to shared
module-sized deltas, converted Ψ to bounded persistent chunks, and added
image-fork/first-declaration benchmark cases. The other registries remain to
be evaluated and converted selectively.

### Stage 3 — module deltas and safe reload

- Extract the exact delta for one successful module.
- Install it into an identical dependency world in memory.
- Recheck stored kernel bindings before committing metadata.
- Differentially compare source-built and image-built worlds and downstream
  elaboration.

### Stage 4 — persistent format and CLI cache

- Add the versioned bounded encoding and full identity header.
- Integrate it with the loader and atomic cache writes.
- Keep generated/mutated suffixes outside the imported image boundary.

### Stage 5 — resident and parallel consumers

- Reuse images in the daemon and test tooling.
- Schedule independent module nodes in parallel.
- Add replay/trusted quick modes only as separately reviewed trust rungs.

## 10. Performance priorities after the image boundary

Image construction is no longer the dominant performance problem. The
prelude fixture currently measures an approximately 88 ns world clone, 385 ns
image fork, and 8.33 microseconds from a fork through its first ordinary
declaration, against about 222 microseconds to rebuild the prelude. The
remaining work therefore separates three costs instead of treating all of
them as "image performance":

1. **First-write detachment.** Add a growth fixture for the first declaration
   which mutates each durable registry. Convert registries selectively from
   those measurements. Provenance is first: every ordinary declaration writes
   it, its entries contain dependency paths and inherited-axiom maps, and its
   whole-table clone may be deeper than the pointer-heavy type indexes.
2. **Dependency replay.** Finish module deltas and safe loading soon enough to
   stop parsing, elaborating, and regenerating unchanged dependencies. A disk
   artifact remains acceleration input rather than a proof verdict; the first
   rung rechecks imported kernel bindings before exposing their metadata.
3. **New-proof cost.** Large x86 and Omega declarations are dominated by
   elaboration, conversion, normalization, and the final kernel gate. Registry
   persistence cannot turn a 96-second isolated theorem target into a fast
   one. Add conversion hit/miss, evaluation, allocation, and repeated-query
   attribution before changing kernel algorithms.

The provisional registry order is provenance, nominal types, traits,
representations, then meta-programs. It is not a mandate to apply one data
structure mechanically. In particular, trait resolution already has queries
which scan candidate tables; its persistent representation should be designed
with secondary indexes by class/member so it improves normal elaboration as
well as suffix detachment. Provenance measurements likewise separate map
detachment from inherited-path construction, since layering fixes only the
former.

Once provenance and the measured large registries are bounded, prefer moving
to Stage 3 over polishing tiny registries whose first-write cost is lost in
noise. In parallel, kernel optimizations should favor untrusted, intra-check
memoization and structural sharing. Persistent admission through
`KernelGate` is a distinct trusted-cache rung and must not be introduced as an
incidental performance optimization.

## 11. Verification and performance gates

Correctness tests must cover ordinary declarations, an inductive with generated
definitions, stored surface re-lowering, traits/instances/designations,
representations, meta-program dispatch, provenance, and failed suffix rollback.
Every source-built/image-built pair must leave byte-identical kernel terms and
the same observable registry behavior.

Performance attribution precedes persistent-format optimization. Record per
module and top declarations for parse, elaborator work, cache hashing, imported
binding recheck, and final gate. The forcing workloads are the Omega arithmetic
prefix and one unrelated standard-library closure. The target is unchanged
dependency loading in seconds rather than minutes; changed-root measurements
remain attributed separately so an import win cannot hide a regression in new
code.

One ungated front-to-back acceptance remains for every shared image family.
Mutation and generated-term controls always operate in a fresh suffix and face
the real kernel.
