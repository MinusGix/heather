# Early cutoff across an upstream edit

Status: implemented for the stale-image lanes (`--accept-stale-images`,
`scripts/test --fast`, `scripts/test --pr`), audited by the exact lane.
Issue: `issues/relocatable-semantic-module-images.md`.
Since `docs/infrastructure/module-dag-design.md`, "the world under a module" is its import
closure in canonical order, not its process's prefix; the cutoff's moves are
unchanged within that world.

## 1. The problem

A module image is keyed by its source and the ordered interface hashes of
every module under it (`ModuleCacheKey`). The interface projection includes
absolute Ψ positions, so appending one theorem to `nat` changes `nat`'s
interface, which changes every later module's key: the whole library
downstream of `nat` is a miss and is elaborated again, although almost none of
it could have observed a theorem it never names.

Early cutoff means stopping that cascade where nothing changed *for the
module*. Two facts make it hard in Heather and shape the design:

- **Kernel terms address Ψ by position.** Global references are de Bruijn
  indices counted from the Ψ length a payload is scoped at. A module
  elaborated over a world with one more binding in `nat` differs from the
  stored one in every index that crosses that binding. "Unchanged" can
  therefore not mean byte-identical; the stored image has to be *moved*.
- **Elaboration reads more than the bindings it refers to.** Name resolution
  sees every declared name; instance search, generated-definition lookup,
  derived instances and the guard copies of lowerings are registries keyed
  by content; `opened` proofs read a dependency theorem's body. Cutoff is
  sound only when everything the elaboration *could* have read is recorded
  and compared, not just what the result refers to.

## 2. What a module observes of its world

When a module misses, the session (`crates/cli/src/semantic.rs`,
`observe_world`) takes two digests of the world under it, both independent
of where anything sits in Ψ:

- **The registry digest.** Each module contributes its delta's events other
  than `Name` and `Global`, plus its scope (`ModuleDelta::registry_part`).
  `RegistryPart::projection` encodes them with every position blanked and
  appends the content hash of what each position named: a referenced
  binding's Merkle interface hash (`crates/cache/src/merkle.rs`), and for a
  kernel payload, the hash of the payload at the Ψ length it is scoped at.
  Modules with no registry events (plain `fn`s and `theorem`s) contribute
  nothing, so adding a theorem to `nat` leaves the digest unchanged; adding an
  inductive anywhere changes it.
- **The name digest.** Two sets of names stand for what the elaboration
  could look up. The identifiers the source text contains
  (`source_identifiers`: maximal runs of alphanumerics, `_`, `'`) cover what
  it wrote. The **lookups** cover the rest: while a module is elaborated,
  every name and module the name tables are asked about is recorded by its
  last `::` segment (`record_name_lookups`, hooked into the table queries in
  `crates/elab/src/names.rs`), and those the source does not spell are
  stored with the image. That is how `+` falling back to `add`, a tactic
  checking for `omega::nat_le_of_not_not_le`, or the function-IR lowering
  asking for `bitvec::BitVec::ofNat` is seen. A declaration slice-replayed
  from the module's previous image (`docs/infrastructure/declaration-slice-replay-design.md`)
  is credited with that image's lookups; a previous image without a record
  leaves the new one without a record. For each declared name whose last
  segment is in either set, `NameWorld::observations` records the declaring
  modules, kinds, and for a global its surface signature and content hash,
  over the names as they stood *before* the module (a snapshot taken at the
  miss). Module names in either set are included too. An upstream
  declaration that collides with any identifier the module wrote, even a
  local binder name, changes the digest. This is the names regime of the
  library: growth may introduce errors but never reinterpretations, and the
  digest is deliberately coarser than resolution.

Beside the digests, a published image carries its **dependency references**
(`ModuleDelta::dependency_references`): every position below the module it
refers to anywhere (bindings, sealed proofs, registry payloads, opened
proofs), each recorded as the defining module, the content hash, and its rank
among equal hashes in that module. Together with the lookups and both
digests these are the image's **world record** (`WorldRecord`, `crates/cache/src/module_image.rs`), stored after the
semantic section, with a `<source key>.src` pointer naming the image last
published for that exact source.

## 3. Moving an image

On a miss under `ImageFreshness::AcceptStale`, `SemanticSession::relocation`
looks up the pointer for the module's source (`load_candidate`), and moves
that image when:

1. its registry digest and name digest equal the current world's, and
2. every recorded reference is found again in the module of the same name,
   with the same content hash and the same number of bindings sharing it.

The second condition builds a map from old dependency positions to new ones.
`ModuleDelta::relocate` (`crates/elab/src/module_relocate.rs`) rewrites the
delta through it: kernel payloads go through `Type`/`Term`/`GlobalBinding::
reindex_global` (`crates/kernel/src/subst.rs`), which renames only free
global indices and refuses when the map does; the module's own positions
shift by the difference of bases. A payload's scope is the one thing that must
be right; the inventory is the exhaustive match in `Mover::event`, so a new
event kind does not compile until it is classified. The guard copies of a
lowering (`GenTyCode`, `GenTyCodeFn`, `GenSpineCodes`, `GenWfSlots`) and a
derived instance's goal name committed definitions only, as constants, so
they have no scope: each constant moves to its counterpart, and a free global
variable is refused.

The moved delta then goes through `replay_module_delta` like any decoded
image, so the kernel (or the verdict store, by content key) judges every
binding, and the registry events face the same preflight. A rejection there
is reported (`RelocationRejected`) and the module is elaborated as usual. A
moved image is published under `SemanticsIdentity::relocated()`, with a fresh
world record, so the next edit can move it again.

Conservative refusals, all of which cost an elaboration and nothing else: any
registry change anywhere upstream; a changed module order or set; a
dependency theorem the module opened whose proof changed
(`OpenedProofChanged`, which the slice path already handles); any name
collision with an identifier the module wrote. A world with more inductives
before the module is a registry change and has to be: nominal tags count the
inductives before them, so the module's kernel terms differ there
(`issues/nominal-tags-from-declaration-identity.md`). The library gate
therefore gives every process one prefix (`docs/archive/library-world-design.md`)
rather than relying on moves between folders.

## 4. Trust

Kernel soundness does not depend on any of this: every moved binding is
rechecked. What the cutoff asserts and does not prove is **faithfulness**:
that elaborating the source over the new world would have produced the moved
delta. It rests on the elaborator reading nothing that §2 does not record.
The argument's weak points are a query that bypasses the name tables'
lookup functions (the hooks sit on every function of `Names` that takes a
name), and elaborator state that is neither a name nor a delta event. Two
gaps of this kind were found while building it, both by tests rather than by
reading: operator fallback names, which the lookup record closed, and
opened dependency proofs, which were moved without being rescoped (the
audit's one byte difference; the replay refused them, so the stale lane
rebuilt the module, but it was a lost cutoff). The audit (§5) is how a next
gap would show.

Because faithfulness is unproven, relocation has the stale lanes' trust
level, not the exact lane's:

- Only `ImageFreshness::AcceptStale` moves images. Those lanes already
  replay images an older compiler wrote.
- The exact lane never moves an image and never replays a moved one: a moved
  image's semantics identity is not the current build's, so the exact policy
  treats it as stale and elaborates.

## 5. The audit

Under the exact policy with `HEATHER_RELOCATION_AUDIT=<file>`, every module
that misses with a candidate image is both elaborated and moved, and one line
per module is appended: `module`, then `same` (identical image bytes),
`same-interface` (equal interface hash, other bytes differ), `refused` (the
cutoff declined, with the reason), or `diverged` (the cutoff let the move
through and the elaboration disagrees with it: the cutoff lied).

`scripts/sentinel` runs it nightly: the library at the last green commit and
at the current one are checked into one fresh store by the current compiler,
the second with the audit on, so every module the stale lanes would have
moved across that day's edits is compared with its elaboration. The report
gives the verdict counts and names any diverged module.
`scripts/sentinel audit [REV]` runs the same comparison by hand.

`HEATHER_RELOCATION_DEBUG=1` prints why each module was not moved (no
candidate, no world record, the digest that differed, the refusal), and
with the audit on writes both images of a `same-interface` module beside the
audit file, for a byte diff.

## 6. Cost

On a miss the session hashes every Ψ binding once (cached across modules)
and the identifiers of the module's source; this is linear in the world and
small beside elaboration. A move costs a decode, a rewrite linear in the
image, and the replay a hit already pays. Publishing adds the world record,
whose size is linear in the module's dependency references. Appending a
theorem to `nat` turns the downstream closure from a near-cold rebuild into
replays and moves, so its cost approaches a warm run plus the elaboration of
the edited module and of the modules that observed the edit.
