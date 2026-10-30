# One world for every process that checks the library

Status: implemented (`heather check --world <dir>`, `crates/cli/src/world.rs`);
the library gate uses `--world lib`.
Issue: `issues/early-cutoff-registry-and-order-granularity.md`.

## 1. Why a folder could not use another folder's images

The library gate (`crates/cli/tests/library.rs`) checks `lib/` one folder per
process, three at a time, through one image store. From a cold store (a fresh
box, a kernel edit, the exact lane after any compiler edit) each child rebuilt
the part of `std` its folder needed, and `lib/native`, whose closure is most
of `std`'s x86 and Linux modules plus the compiler, went over the CPU rail.
Two things made a module's image one process's alone.

- **The lint profile was the root's.** `check` took the profile from the path
  it was given (`lib/std/...` is `Stdlib`, anything else `Default`) and keyed
  every module of the closure with it. The profile is part of the image key,
  so `nat` checked from `lib/std/num` and `nat` checked from `lib/native` or
  any `lib/_tests` folder were two keys. It is now the module's own
  (`loader::Module::lint_profile`), and `SemanticSession::check` sets the
  elaborator's profile from the one it keys by, so the two cannot disagree.
- **A module's world is everything loaded before it.** An image is keyed by
  the ordered interfaces of every module before it in its process: Ψ
  positions are absolute, and an inductive's nominal tag is the count of
  inductives before it, which each constructor carries in its kernel type
  (`inductive::tag_type`). A folder's process loads its folder's closure in
  its own depth-first order, so one module sat over different prefixes in
  different folders. Those are different elaborations, not one elaboration
  at different addresses: an extra inductive earlier moves every later tag,
  and the kernel terms differ. The early cutoff cannot move such an image
  either, and its registry digest says so (`the world's registries differ`
  was the refusal for nearly every module a folder did not build itself).

## 2. The world

`World::of(dir)` is one order of the library's **shared** modules, those
another module under `dir` imports. A check over it (`--world dir`) loads the
order up to the last shared module the root's closure needs, then the root's
own modules. Every process naming the same world therefore gives each shared
module the same prefix, and its image has one key: the first process to need
it builds it (the store's single-flight lock makes a concurrent asker wait),
and every other one replays it. A module nothing imports (a test module, a
leaf of the library) is not in the world: it is loaded after the prefix, so
its key depends on its own process, which is the only one that checks it.
A module that only a command reads, not another module (`native_tools` and
`native_build_parts`, which `write-elf` loads), is then keyed apart in the
gate and in that command, and the command's first run elaborates it again;
a `lib/_tests` probe that imports it makes it shared, and the gate's
`write_elf_loads_only_world_modules` holds `write-elf`'s closure to the world
(`issues/native-process-fixed-cost.md`).

The order is built folder by folder (`world::folders`: a directory holding
`.hthr` files is a folder with everything below it; one holding only
directories is split into them). Repeatedly the folder whose closure needs
the fewest shared modules not yet placed, the earlier on a tie, places them in
its own load order. A small closure thus finds its modules near the front
instead of behind modules it never reads. The gate checks its folders in the
order the world placed them (`World::folders`), so a child finds the modules
in front of its own already built by the children before it.

## 3. What it costs

A process now replays the shared modules in front of its last needed one
that it does not itself need. Over the current library that is a bit under
twice the module replays of the folders' own closures; a replay is a decode
and the verdict store's lookups, small beside an elaboration. Cold, every
shared module is elaborated once in the whole gate instead of once per
folder whose closure holds it.

The world is a function of the tree. Adding a module nothing imports changes
nothing; a new import edge can change which folder places first, which moves
every later module's prefix. The exact lane then rebuilds what moved, and the
stale lanes' early cutoff refuses a reordered world as it refuses any changed
registry (`docs/module-interface-cutoff-design.md` §3), so such an edit costs
a rebuild of the moved suffix once. Computing the world reads and parses the
library's files once per process.

A process that needs the world's end and runs alone builds the whole front
of it alone. The gate's children do not: they run in the world's order, three
at a time, so the front is built once among them. A lone process does: a
`write-elf` of cat, whose closure sits at the world's end, would have to
elaborate most of the library over cat's own modules and its certificate,
past the CPU rail on a cold store.

Until 2026-10-27 `write-elf` and the suite's CLI image warmup therefore
stayed on their own closure's order. That cost a cold store cat's closure
three times: once for the gate, once in cat's order, and once more in
`native_tools.hthr`'s, whose closure is cat's in another order, so it shared
almost no image with either. Each of the last two was one process of about
250 CPU-s, close to the rail (`issues/library-gate-native-cold-rail.md`).
Now `write-elf` takes `--world` as `check` does, the native tests pass
`--world lib`, and the warmup before them is the gate itself
(`scripts/test`'s `cli_images_warmup`), which builds the front a folder per
child. Over the gate's store a `write-elf` replays its whole closure; the
world's prefix costs it a few CPU-seconds of replays beyond its own closure.

The showcase gate's rows (`crates/cli/tests/showcase.rs`) stayed on their own
order until 2026-10-30, so the three algebra clients (`creal_client`,
`ordered_field_client`, `semiring_client`) re-elaborated `rat`, `creal`,
`ordered_field` and their prefixes from source after the gate had built them,
which was nearly the whole cost of the target over a gate-warm store.
They pass `--world lib` now and replay the gate's images; only the row's own
module, which no world holds, is elaborated, and a gate-warm target is a small
fraction of its former CPU.

## 4. What it does not do

It makes the prefixes equal; it does not make a module's elaboration
independent of modules it does not import. Two things would, and together
they would let each process load only its own closure:

- **Nominal tags from the declaration, not the count.** A tag derived from
  the inductive's qualified name (with collisions refused) would make a
  module's kernel terms independent of how many inductives came before it.
  This is also what an added inductive costs today: every later tag moves,
  so everything after it is a different elaboration, which no registry
  granularity in the early cutoff can avoid.
- **Observing only the closure.** Registries (instances, designations,
  derived instances, evidence rules) are global and some reads scan them,
  and the name digest records declarations from every module in the world.
  The early cutoff would have to digest what the closure contributes and
  what the elaboration asked of the rest, as the issue's first bullet
  proposes for registries.
