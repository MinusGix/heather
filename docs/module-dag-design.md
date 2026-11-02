# Building library modules in dependency order

Status: built (§9, §11, §12), measured (§10).
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

The gate first builds, then checks (§12). `heather check --build-jobs 4
--build-only lib` elaborates every module that has no image, each in a
`heather check` of its own, four at a time, a module once its closure's
images exist and the longest remaining chain first. Then four children at a
time check one folder each, in `World::folders` order, over a store that
holds every module that can be built: they replay, and report each module's
warnings and matched refusals, and the errors of a module the build step
could not build, which they elaborate again to say why.

What bounds the cold gate is then the import graph's critical path (the
longest chain of elaboration cost through imports, which is the native
compile chain) and the width, not the sum, and a module's CPU rail covers
that module and the replay of its closure, never another module's
elaboration.

An earlier form of this design let each folder child build whatever of its
closure no child had built yet, setting aside a module another process held
the build lock of (`ModuleImageStore::being_built`; `heather check` still
does this within one process). It was shorter cold, because no module's
closure was replayed by a process of its own, but who built a shared module
was a race, and the race decided which child's rail paid for it: a cold
suite killed `lib/_tests/std/tactic`, which had built half the tactic
library beside `lib/std/tactic`'s child, and a PR-lane run killed
`lib/native` the same way. Ordering the folders (library, then tests, then
native) kept both under the rail on the box, but a heavy folder could still
lose the race.

A module that fails no longer turns images off for the rest of the process.
Its dependents are refused with a note naming it ("its import closure holds
`X`, which did not check"), and modules that do not import it go on as
before. The build step leaves a failed module's dependents unbuilt, and the
folder check reports it.

## 8. Memory

A process holds the worlds of its closure: the modules on the
largest-import chains are shared, and a remainder module is one extra copy
per world it is moved into. A build process (§12) holds one closure, of
one module. A folder child holds the worlds of every module of its folder,
and a test folder's roots are imported by nothing, so before the session
was told its load each root's world, with its moved copies, stayed to the
end of the process.

`SemanticSession::expect_load` takes the modules the driver will check,
with their imports. The session then keeps a finished module's world only
while a module still to come imports it directly (only a direct import can
be a world's base, §6), and its delta, registry part and hashes only while
one holds it in its closure; at zero they are dropped. A wrong list costs
time, never a verdict: a dropped world is built again (`state_of`) and a
dropped delta decoded again from the store, and a session without a store
keeps every delta. `heather check` passes its load.

Measured cold on the cloud box (4 CPUs, 15 GB), the whole gate at three
and at four jobs, peak resident memory per process and summed over all of
them:

- The largest process is a build process of one test module over most of
  the tactic library, a little under 2 GB, and the four largest are all
  build processes. Dropping worlds does not move them: one closure is what
  such a process is for.
- Folder children were never the peak. Dropping worlds takes the largest
  ones down by an eighth to more than a quarter (`lib/_tests/std/tactic`
  most).
- Summed over all processes the peak stays under 3 GB at four jobs as at
  three: the heavy builds do not overlap more. Since §12 each build process
  holds one closure, and memory no longer bounds the width; the earlier
  doubling to 5–6 GB (`issues/library-gate-warmup-runs-alone.md`) was
  folder children building wide closures with kernel width above one.

So the gate runs four wide, one process per CPU. Cold, the build step takes
about a fifth less wall time than at three; the warm folder checks are
unchanged.

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
- **Warm** (every image present) CPU was unchanged by §2–§6: it was
  dominated by the refusal-test modules, which were re-elaborated every run.
  With their images (§11) the warm gate takes about half the wall time and
  about two fifths less CPU.
- **Building ahead** (§12): the cold gate is about a fifth longer than the
  racing children's and about a quarter more CPU, from the build processes'
  closure replays, and still about a third shorter than the chain; every
  child stayed far under its rail.
- The sequential elaboration sum over the library is several times the
  critical path, so with three workers the gate is now width-bound, not
  chain-bound; more width would help only as far as memory allows (§8).

## 11. Expected refusals have images

A `lib/_tests` module states refusals as `// expect-error` directives
(`crates/cli/src/expect.rs`). Before, its refused declarations were errors
to the session, so the module never had an image, was elaborated again on
every run, and stopped anything that imported it. Most of a warm gate was
those modules.

Under `--expectations` the session judges a module with directives itself
(`SemanticSession::with_expectations`). It elaborates it whole
(`Elaborator::check_module_delta_refusing`, which keeps the delta of what
checked: a refused declaration registers nothing), judges the errors
against the directives, and when every refusal is the one its directive
names and nothing else failed, publishes the delta with the count of
matched refusals in the image header. The module then counts as checked,
and its dependents are checked over what did check. A module that misses its
directives is an ordinary failure and has no image.

A refusal is the elaborator's verdict, which no kernel recheck can
reproduce, so such an image is replayed only

- by a session that judges directives: a plain `heather check` of the same
  module elaborates it and fails, as before;
- when this build wrote it: the stale lanes elaborate it again, since an
  older compiler's refusal says nothing about this one's;

and it is never moved to another world (the early cutoff) or sliced from
(the declaration-slice replay), both of which would assert the refusal
carries over.

## 12. Building ahead

A module's key is its source, its lint profile and the interface hashes of
its closure's images (§5), and every image header records its interface hash
(`ModuleImageCache::recorded_interface`). So the keys of a whole load can be
computed by reading headers in import order, without decoding an image: a
module whose closure is all built has a key, and is built when the store
holds that key (`semantic::BuildPlan`). The planner uses the session's own
canonical order (`canon_over`), so the two agree on every key; a module
whose build does not land at the planned key is not retried.

"Built" here has to mean what a load accepts, or the closure above a
module the planner counts and the load refuses falls to whichever process
loads it, one folder child elaborating it all under one CPU rail. The key
covers the image and interface encodings' versions, so a format bump is a
miss for planner and load alike, and the header read also checks the
semantic section's version. Until 2026-11-02 neither did: under the stale
lane, after #359/#360 bumped the format, a seeded store's old images read
as built while every load rejected them, and `lib/_tests/native`'s child
met the rail on #358, #359 and #366
(`issues/library-gate-native-tests-fresh-box-rail.md`).

`heather check --build-jobs N` runs the planner over the load before
checking and starts a `heather check` of the module's file (with the
parent's `--expectations` and image policy) for each ready module, up to N
at a time, in order of the longest chain of source bytes above it,
refreshing the plan as each finishes. `--build-only`
stops there. A module that fails is reported with the tail of its output; its
dependents stay unbuilt, and the ordinary check that follows reports it.

`--build-first <dir>` (repeatable) starts the modules below the named
directories, and their closures, before any other ready module. The gate
names `lib/native` and `lib/_tests/native`, the folders the test runner
waits on before it starts the native gates. `--build-times <file.tsv>`
writes a row per built module: when it became ready (the end of the
last import built in this run), when it started and finished, and the
import that readied it. Following `readied_by` back from the last row
gives the chain that set the step's length, and the gap between `ready_s`
and `start_s` is time spent waiting for a job.

Measured cold on a 4-CPU cloud box (master f9c6e9d, gate settings, 218
modules), the step is CPU-bound, not chain-bound: about 820 CPU-s in about
220 s of wall, within a tenth of the four-core floor. The longest chain ran
through the interval tactics to `interval_tactic_real_tests`, and part of it
was waiting for a job. The native chain (`native_compile` through
`native_compile_correct`) was done by 89 s, and no native module took more
than about 12 s. Ordered by source bytes alone, the native folders' modules
still waited behind the std test chains and were last built at about 200 s.
With `--build-first` they were built by about 99 s, and the step's length
and CPU did not change (`issues/native-closure-builds-first.md`). So
splitting a long module does not shorten this step: the step has no chain
to shorten, and each new module adds a closure replay.

The price is replay: each build process replays its module's closure, so the
build step replays every closure once (§2's sum, about eighteen times the
module count over the library) where folder children replayed about three
times it. Replay is dominated by the Merkle walk that lets the verdict store
vouch for a replayed binding, and it is what makes the build step's CPU
higher than the racing children's.

## 13. Vouching for a whole replay

A replay asks the verdict store about every binding it rechecks, and the
store answers by Merkle hash, so each replay hashes its whole extension
along the chain (`Inner::sync`) before a single verdict comes back. When
the same image is replayed over the same world again, every one of those
questions has the answer it had last time.

So a replay that rechecked clean records one verdict for the whole replay,
keyed by

- the decoder's build (`SemanticsIdentity::current`): an image another
  compiler wrote, replayed by a stale lane, never matches;
- the world under the module: its length and each module's name and
  identity, in order;
- the image's content hash (`LoadedModule::content`, over the semantic
  section).

The next replay with that key is not rechecked at all. "Clean" is the
per-binding store's own rule: no check unsealed a proof, and no body went to
the deferred pool (whose verdict the replay does not wait for). A replay
that was not clean records nothing and is rechecked every time, as before.

A replay over the module's **own canonical world** (the cache hit of the
module itself, and an import loaded where the map is the identity,
`over_prefix`) is keyed as above. A **moved** replay (§4) is keyed by the
same parts plus the world the stored positions were counted in: the
module's canonical world, by name and identity, beside the world it is
moved into. The move is a function of those two orders and the modules'
binding counts, and the decode a function of the bytes and the build, so
the key fixes the moved delta and the Ψ it is replayed over; the replay
that recorded the verdict rechecked exactly those terms, binding by
binding. Nothing about `relocate` is trusted beyond determinism: a wrong
move would have failed that first recheck (or passed it as the terms it
actually produced, which are the ones the next replay produces again).
All three places that move an image key its replay this way
(`load_into`, `into_process`, `hit_into_process`). Until 2026-10-30 moved
replays kept the per-binding path, and on a tactic-test module they were
the Merkle walk that was left.

The cost it removes is the hashing, which grows with the replayed
extension; decoding, the move itself, and the replay's other rechecks
(statement and registry checks that are not verdicts) stay. On a
tactic-test module whose closure is large, vouching for canonical replays
made a warm check about a sixth faster and halved the Merkle walk;
vouching for moved ones took the rest of the walk and about another sixth,
and no declaration is asked about one at a time. What a warm check of such
a module is left with is mostly the move (`image_relocate_ns`, which times
these moves as well as the early cutoff's), then decoding
(`issues/warm-replay-relocate-cost.md`). On a module whose replay is
dominated by decoding the change is lost in the noise. The `ok` line says
`(N vouched for whole)`.
