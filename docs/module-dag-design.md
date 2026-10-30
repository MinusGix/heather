# Building library modules in dependency order

Status: design, staged implementation (§9).
Issues: `issues/module-dag-build.md`, `issues/nominal-tags-from-declaration-identity.md`.
Supersedes `docs/library-world-design.md` §2 (the world) once §9's stages land.

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
   one key. Two classes of entry differ here:
   - **Content caches**: the generated definitions keyed by a tag (`GenDef`,
     the guard copies `GenTyCode`/`GenTyCodeFn`/`GenWfSlots`/
     `GenSpineCodes`/`GenFamLevels`) and representation monomorphs. A family
     over an index type from another module registers that index type's code
     (`register_idx_code`); two sibling families each register one. Each
     copy stays at its position, and the terms of the module that made it
     keep naming it. The index keeps the copy that came first in
     `canon(M)`, after checking that the two copies have the same content
     hash; differing content is a conflict. Today the second family would
     have found the first's copy, because its process loaded the first
     family's module before it whether it imported it or not.
   - **Declarations**: instances, classes, designations, evidence rules,
     derived instances, implementations, accesses, meta programs. Two
     modules that each declare one for the same key are incoherent, and the
     first world that holds both refuses: the replay of the later one fails
     with the conflict, reported at `M` as an error naming both modules.
     Before this design such a pair could not both check in one process at
     all, so the library has none.

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

The image records its canonical module list and each module's binding count
beside the world record, so a load can compute the move of step 1 and check
it against the process's own computation before decoding.

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
Each child checks one folder: it walks its closure in topological order and,
for a module with no image yet, tries the module's build lock without
blocking. A module another child is building is set aside and the child goes
on with any module whose dependencies it has; it blocks on a lock only when
nothing else is ready. The single-flight lock still makes every module an
elaboration once in the whole gate.

What bounds the gate is then the import graph's critical path (the longest
chain of elaboration cost through imports), not the sum.

## 8. Memory

A child holds the snapshots of its closure: the modules on the
largest-import chains are shared, and a remainder module is one extra copy
per world it is moved into. That is no more than today's child, which holds
the world prefix up to its last needed module. Three children run at a time
as before; giving them more width is what doubled peak memory to 5–6 GB
before (`issues/library-gate-warmup-runs-alone.md`), and this design does not.

## 9. Stages

1. Tags from the declaration (§3). Changes every image; the format version is
   bumped so no image of counted tags is replayed into a world of hashed
   ones.
2. Closure worlds in `SemanticSession` (§4–§6): canonical orders from the
   loader's graph, closure keys, moved loads, duplicate content caches.
   `--world` becomes a no-op, kept for callers, and `World::of` survives only
   as the gate's folder order.
3. The gate's scheduling (§7).

What goes away with stage 2: `write_elf_loads_only_world_modules` and
`WRITE_ELF_IMPORTS`'s reason to exist (every process keys every module the
same way), the showcase rows' `--world lib`, and the early cutoff's
"module order" refusals (its registry digest is over the closure).
