# Building library modules in dependency order

Status: built (§9), measured (§10).
Issues: `issues/module-dag-build.md`, `issues/nominal-tags-from-declaration-identity.md`.
Supersedes `docs/library-world-design.md` §2 (the world).

## 1. Why the gate is a chain

The library gate (`crates/cli/tests/library.rs`) runs three `heather check`
children at a time over one image store, and still keeps only about 1.6 CPUs
busy (`issues/library-gate-warmup-runs-alone.md`). Each child loads the
library's world (`docs/library-world-design.md`) up to the last shared module
its folder needs, and a module's image is keyed by every module before it in
that world. So a module can be built only after every module in front of it
has been, by some child, and the children spend their time waiting on one
another's single-flight locks along one line.

Three things make a module's elaboration depend on everything loaded before
it, not only on what it imports:

- **Ψ positions are absolute.** A global is a de Bruijn index into one flat
  telescope, so a module's kernel terms name its dependencies by where they
  sit, and a different prefix is different terms.
- **Nominal tags count.** An inductive's tag was the number of inductives
  committed before it (`Types::commit`), and every constructor carries it in
  its kernel type (`inductive::tag_type`). Two modules built apart hand out the
  same tags.
- **Registries are global.** Instances, designations, evidence rules, derived
  instances, representations, meta programs and the generated-definition
  caches are visible to every later module of the process, imported or not.
  Names are not: resolution is by the module's own imports
  (`crates/elab/src/names.rs`).

The first is a matter of addresses, which relocation already handles
(`ModuleDelta::relocate`, `docs/module-interface-cutoff-design.md` §3). The
other two are semantics: they decide what the module *means*.

## 2. The rule

**A module is elaborated over its import closure and nothing else, in its
canonical order.** Its image is keyed by its source and the identities of
that closure, and it is loaded into any other world by moving it there.

The canonical order `canon(M)` of a module's closure is a function of the
import graph below `M` alone:

- Let `B` be the import of `M` with the largest closure (the
  lexicographically least name on a tie). `canon(M)` starts with
  `canon(B)`, then the rest of the closure in depth-first post-order over
  `M`'s other imports in sorted order, skipping what is already placed, then
  `M`.
- A module without imports is the prelude's bindings then itself.

Choosing the largest import first makes `canon(B)` a prefix of `canon(M)`,
which is what lets a process reuse `B`'s world for `M` (§6). Over the current
library (207 modules, 123 imported by another) the closures sum to 3682
modules, and the parts of them outside the largest import's closure to 166.

What a module can observe is then fixed by what it imports:

- **Names**: unchanged, already by import.
- **Registries**: only entries contributed by modules in its closure (and the
  prelude). Before, a module also saw whatever its process happened to load
  before it; under the world, everything in front of it in `World::order`.
  This is the visibility rule of Lean and Rocq (instances of transitively
  imported modules), and it is the one that lets an image mean one thing.
  A module that used an instance it does not import now fails where it uses
  it, and is fixed by importing the module that declares it.
- **Tags**: §3.

## 3. Nominal tags from the declaration

A tag is a 32-bit hash of the declaration's qualified name,
`module::Name` (`types::declaration_tag`); the `IWf` route's shape
declaration is `D#shape`, so it has its own. The prelude's
`CollectionLiteral` keeps its reserved tag, which the hash never yields.

A tag still has to be unique in every world that holds the declaration, so a
collision is **refused**, never probed onward: probing would make the tag
depend on what was committed first, which is the property being removed. At
elaboration the second declaration is an error naming both
(`elab_inductive`); at replay it is the `nominal-type` metadata conflict the
preflight already raises (`preflight_module_event`). Module names are unique
in a loaded closure (the loader refuses two files with one stem), so two
declarations share a qualified name only if they are the same declaration.
With `n` inductives in a world the chance of any collision is about
`n²/2³³`; at the library's few hundred it is a few in a hundred thousand, and
a hit costs a rename.

The tag is a compact `NatLit` either way, so a large one costs conversion
nothing over a small one (`issues/nominal-tag-conversion-cost.md` measured
the tag's *shape*, not its magnitude). No reader assumes an order: the only
place a tag was predicted before its commit was the `IWf` skeleton's
`next_tag`, now the shape declaration's own hash.

## 4. Composing images built apart

A process checking `M` builds `canon(M)` from the images of `M`'s closure.
Each image `D` was built over `canon(D)`, which is generally not where `D`
sits in `canon(M)`. Loading it there is three steps, all exact.

1. **Moving it.** Every module of `D`'s closure occupies one contiguous range
   in `canon(D)` and one in `canon(M)`, with the same layout inside (an
   image's bindings are a vector, replayed in order). The map from old
   positions to new ones is therefore determined module by module from the
   two orders and the modules' binding counts; nothing is matched by
   content and nothing can be missing. `ModuleDelta::relocate` rewrites the
   delta through it; when the map is the identity (`D` on `M`'s
   largest-import chain, the common case) the decoded delta is used as is.
2. **Replaying it.** `replay_module_delta` as for any image: the kernel
   rechecks every binding, or the verdict store vouches for it by content
   key, which a move does not change (the Merkle hash names references by
   content). Soundness never rests on the move.
3. **Merging its registries.** Two images built apart can carry entries for
   one key, and the first world that holds both refuses: the replay of the
   later one fails with the metadata conflict the preflight already raises,
   reported at `M` as an error naming the module. This holds for both
   classes of entry:
   - **Declarations**: instances, classes, designations, evidence rules,
     derived instances, implementations, accesses, meta programs. Two
     modules that each declare one for the same key are incoherent.
   - **Content caches**: the generated definitions keyed by a tag (`GenDef`,
     the guard copies `GenTyCode`/`GenTyCodeFn`/`GenWfSlots`/
     `GenSpineCodes`/`GenFamLevels`) and representation monomorphs. A family
     over an index type from another module registers that index type's code
     (`register_idx_code`), so two sibling families over one foreign index
     type would each carry a copy. Before this design the second family
     found the first's copy, because its process loaded the first family's
     module whether it imported it or not. Keeping the first copy after
     checking the two have one content hash would be sound; it is not built,
     because the library has no such pair (every folder checks under the new
     rule), and a refusal is the conservative answer until one appears
     (`issues/module-dag-build.md`).

The state a process reaches for `canon(M)` is a function of the images of
`M`'s closure and their order, and each image is a function of its key
(inductively, by §5). That is the whole faithfulness claim, and it is by
construction: nothing asserts that re-elaborating `D` at its position in
`canon(M)` would give the moved image. It need not, because `D` is *defined*
as its elaboration over `canon(D)`. This is why closure keys are exact-lane
material, unlike the early cutoff's moves, which assert that elaborating a
module over a changed world would reproduce the moved image
(`docs/module-interface-cutoff-design.md` §4).

## 5. Keys

`key(M) = H(source(M), lint profile, [identity(D) for D in canon(M) without M])`
where `identity(D)` is `D`'s name with the interface hash of its image in its
own canonical coordinates. That interface already chains `D`'s own key, so the
keys form a Merkle DAG over the import graph: editing a module changes the
keys of exactly the modules that import it transitively. Adding a module
nothing imports, or an import edge elsewhere in the library, changes nothing
for `M`, where the world reordered every later module's prefix.

The image does not need to record its canonical order: the key already
fixes it, and the process computes the move of §4 step 1 from the two orders
and the binding counts of the modules it has finished. A decoded image whose
length disagrees with that computation is refused as an internal failure,
never moved.

## 6. Worlds inside one process

A process checks its roots' closure in a topological order. For each module
it needs the state after `canon(M)` without `M`: to replay `M`'s image there
(a hit), or to elaborate `M` there (a miss). The session keeps, for every
module it has finished, the elaborator's semantic image after `canon(M)`
(`Elaborator::semantic_image`, a persistent snapshot that shares Ψ and the
layered registries with the snapshot it extends). `M`'s world is `B`'s
snapshot extended by the modules of `canon(M)` after `canon(B)`, each loaded
by §4, and then `M` itself. So a process that loads a closure of `n` modules
replays about `n` images plus the sum of those remainders, which over the
library is 166 in all; a folder's closure today replays nearly twice its
size (`docs/library-world-design.md` §3).

The per-module bookkeeping that the early cutoff keeps for "the world under
the next module" (the session's `world` and Merkle vectors) belongs to the
snapshot, since each world is a different sequence; the Merkle hashes of a
binding are content hashes and are cached by binding.

## 7. The gate

With closure keys the gate's children no longer have to follow one order.
The gate still runs three children at a time, one folder each: the library's
folders first and `lib/_tests`'s after, each part in `World::folders` order,
then `lib/native` and `lib/_tests/native`. Inside a child, `heather check` walks its modules in
a topological order of the written imports and, among the modules whose
imports it has finished, takes the first that no other process is building
(`ModuleImageStore::being_built`, a non-blocking try of the build lock). Only
when every ready module is being built elsewhere does it take one anyway and
block on its lock. The single-flight lock still makes every module an
elaboration once in the whole gate.

What bounds the gate is then the import graph's critical path (the longest
chain of elaboration cost through imports, which is the native compile
chain), not the sum.

The folder order matters for the rail, not for the sum. A child builds
whatever of its closure no other child has built yet, under its own 300 s
CPU rail, so who builds a shared module is now a race. With the old order a
cold suite started `lib/_tests/std/tactic` beside `lib/std/tactic`; the test
child built half the tactic library and died at the rail, though alone and
cold it costs the same CPU on both designs. A test folder's closure is mostly
library, and its own modules are its heaviest, so starting the test folders
after the library's keeps each test child paying for its own modules.
`lib/native`'s own modules alone come near the rail
(`issues/native-gate-child-cold-at-rail.md`); started early, it lost the
same race in a PR-lane run, so it goes last, when the rest of its closure is
built, as it did in the chain. In a simulation over measured per-module
costs that costs the cold gate a few percent against library-first alone,
and waiting on whole folders instead (a folder starts when the folders of
its closure finish) costs about two fifths, because it gives up the
module-level overlap; largest-first was worse for the rail.

A module that fails no longer turns images off for the rest of the process.
Its dependents are refused with a note naming it ("its import closure holds
`X`, which did not check"), and modules that do not import it go on as
before.

## 8. Memory

A child holds the snapshots of its closure: the modules on the
largest-import chains are shared, and a remainder module is one extra copy
per world it is moved into. That is no more than today's child, which holds
the world prefix up to its last needed module. Three children run at a time
as before; giving them more width is what doubled peak memory to 5–6 GB
before (`issues/library-gate-warmup-runs-alone.md`), and this design does not.

## 9. What was built

1. Tags from the declaration (§3). The module image format version is bumped,
   so no image of counted tags is replayed into a world of hashed ones.
2. Closure worlds in `SemanticSession` (§4–§6): canonical orders from the
   written imports, closure keys, moved loads (`ModuleDelta::relocate`, or
   `over_prefix` when the map is the identity), per-module snapshots
   (`Elaborator::fork_over`). `heather check` runs without a process world
   (each module's world is canonical, nothing accumulates); `--deny-axioms`
   and the library callers that need one process-wide state keep the process
   world, into which each finished module is moved.
3. The child's scheduling (§7).

`--world` is accepted and ignored, for the scripts that pass it to older
binaries (`scripts/bench-probes` A/B runs). `World::folders` survives as the
gate's folder order. `write_elf_loads_only_world_modules` is gone: every
process keys every module the same way.

## 10. Measurements

Cloud box (4 CPUs), the library gate's driver run by hand over a cold image
store, three children, 300 s CPU rail, master against this design, same
build profile. Shapes, not numbers (`CLAUDE.md`):

- **Cold wall time** drops by about two fifths with the old folder order, and
  by about half with library folders first (§7). CPU time drops a little
  (fewer duplicate replays: a folder's closure replays about its own size,
  not nearly twice it).
- **Peak memory** across all children rises by about a third, and the
  largest child by about a tenth: children now overlap heavy folders that
  the chain kept apart. It stays well inside the 6 GiB per-process rail.
- On master the `lib/_tests/std/algebra` child died at the CPU rail cold,
  waiting behind the chain; under closure keys it checks.
- **Warm** (every image present) CPU is unchanged; it is dominated by the
  refusal-test modules, which are re-elaborated every run.
- The sequential elaboration sum over the library is several times the
  critical path, so with three workers the gate is now width-bound, not
  chain-bound; more width would help only as far as memory allows (§8).
