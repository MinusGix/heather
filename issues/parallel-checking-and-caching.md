---
title: "Parallel checking and the certified cache: many agents, one telescope"
status: open
labels: [tooling, design, performance, cli, meta]
created: 2026-08-06
updated: 2026-08-06
---

Design sketch (discussion 2026-08-06, nothing prototyped): how N concurrent
sessions — human or agent — edit and check different parts of the library
without copying the repo per session, and how a check's result is cached,
trusted, and merged. Written down now so the load-bearing invariant and the
format decisions are designed *for* from the start rather than retrofitted.

## What this issue owns

The parallel-checking and caching design: the interface-split invariant, the
content-addressing scheme, the trust ladder (with certificate replay as the
agreed direction), the daemon/shared-telescope architecture, the command
split, and the merge semantics. Everything it needs from elsewhere is a
named assumption below.

## The load-bearing invariant: proofs are opaque

A theorem's downstream interface is its **statement**; no consumer ever
needs the proof body. Definitions are the only declarations whose bodies
leak downstream (δ in conversion). So a declaration's *interface* is:

- **theorem**: name + statement. Proof-body changes are invisible to every
  dependent.
- **fn / def**: name + type + body (the body is conversion-relevant).
- **inductive**: the whole declaration (its generated defs derive
  deterministically from it).

Two sessions' work merges cleanly **iff their interface deltas commute**:
disjoint new names, no edits to shared statements or def bodies. Proof
iteration — most of what any session does — never touches an interface.
Lean 4.9+'s intra-file parallel elaboration is the small-scale confirmation
(bodies don't feed forward); this design applies the same fact
repo-wide.

## Content addressing: a Merkle DAG over elaborated declarations

The precedent is **Unison**, not Zig: a declaration's cache identity is the
hash of its *elaborated* form with every global reference replaced by the
hash of the referenced declaration's interface. Names are metadata over
hashes. Consequences: renames invalidate nothing; source refactors that
elaborate identically invalidate nothing; merge is DAG union.

This shape is forced, not just nice: the kernel context is a **nameless
telescope**, so Ψ indices are positions and any cache keyed on position dies
the moment a merge inserts a declaration and renumbers the suffix. Hashing
with references-replaced-by-referent-hashes makes keys position-independent;
the telescope stays the kernel's view, the DAG is the build system's.

Invalidation is rustc/Salsa's red-green rule: on upstream change, re-run and
compare *output* hashes before invalidating downstream — so a strengthened
proof under an unchanged statement invalidates nothing, by construction.

## The trust ladder, and the direction chosen

The cost profile today is kernel-dominated (the heavy file is ~99% kernel
gate — docs/frontend-benchmarking.md), so incrementality that re-runs the
kernel on unchanged declarations saves little; a useful cache must let a run
*skip* the kernel, which makes the trust question unavoidable. Three rungs:

1. **Trust the hash-keyed cache** (Lean's `.olean` model): entry =
   (interface-closure hash → kernel-accepted). Trusted base grows by "the
   OS gave us a real, unforged file". Acceptable for inner loops; never for
   the final gate.
2. **Certificate replay** — **the agreed design direction (2026-08-06)**:
   cache the *search*, not the verdict. Conversion dominates kernel cost
   (fuel, unfold choices, strip decisions); a check that emits a trace of
   those decisions lets a recheck replay them — the kernel re-judges every
   run, but search becomes a guided walk, plausibly near-linear. The
   success case returning its search state is the same feature as
   [[ai-facing-tooling]]'s failure case; the replay artifact is that state
   serialized. **The trace hook and format are designed for from day one
   even if v1 ships as rung 1** — cheap to leave room for, miserable to
   retrofit.
3. **Certified cache, post-bootstrap**: once the compiler is
   Heather-in-Heather, a cache artifact carries a proof about itself and
   the boundary narrows to kernel + file integrity. The build cache
   becomes one more compilation target that owes a certificate.

Caveat on the ratio (discussion, 2026-08-06): kernel-dominance is partly an
artifact of a still-simple elaborator and sub-Lean-scale files. Kernel
optimization rounds will shift it, and Heather-in-Heather shifts it further
(more room to trust kernel optimizations). The design should not assume the
99% number is permanent — rung 2 is chosen partly because it stays sound
whichever way the ratio moves.

## Architecture: don't copy repos — share the telescope

RAM answer is copy-on-write at the *context* level, not the filesystem.
Imports already flatten into one telescope prefix; a daemon holds the
elaborated prelude + library Ψ once, each session forks it O(1) and appends
its own suffix. Suffixes from different sessions are independent by
construction when neither references the other — exactly the common case
(one session on List lemmas, another on sorting proofs). N sessions cost
one shared library plus N deltas.

This converges with [[context-representation-clones]]: the shared-spine
representation that issue wants for single-threaded perf is the same data
structure this design needs for forking. One round buys both.

"Errors outside your code" stops being a prompting hack and becomes a
protocol: a session *is* a suffix over a pinned prefix hash; diagnostics
outside the suffix are impossible to cause and trivially attributable.

## The command split

Precedent: Coq's `vos`/`vok`/`vo`, importing its scar deliberately.

- **`heather quickcheck`** — elaborate + kernel-check *your suffix only*
  against cached upstream interfaces (rung 1, or rung 2 replay where traces
  exist). The agent/inner loop, multiprocess-friendly. Never accepts a
  proof wrong relative to its assumptions — the kernel runs on everything
  the session wrote; the risk is confined to stale/forged upstream cache.
- **`heather check`** — full pass over the closure; cache entries re-earned
  (replay where available, from scratch where not). The merge and CI gate;
  today's `heather check` semantics.
- **`heather build`** — check + codegen through the certifying compiler.

The Coq scar: `vos` hurt people because a green partial check *looked like*
a green full check. Trust level is therefore part of the output and the
cache metadata ("checked against 14 cached interfaces, 3 unverified this
session"), so a merge gate can mechanically demand zero unverified
interfaces.

## Merge semantics

Union the declaration DAGs; conflict = same name, different interface hash
(reject or rebase); re-check only declarations whose interface closure
changed. Disjoint-closure sessions merge at cost O(what was added). The
same-file case reduces to the same machinery once identity is hash-based —
the file is just a serialization order.

## The metatheorem underneath (the ambitious end)

Soundness of "merge = union + renumber" is **Ψ-weakening plus
strengthening**: extending the global context with well-typed declarations
preserves every judgment, and a declaration's check depends only on the
prefix it references. [[prog-extension-lemma]] is the same linking
statement one level down, in the IR — same proof shape, one for the
runtime, one for the build system. Post-bootstrap, the incremental
checker's core invariant ("interface-closure hashes equal → verdicts
equal") is a stateable, provable theorem about the compiler: an
incremental cache whose invalidation logic is *verified*. Not exotic —
substitution lemmas wearing a build-system coat.

## Lessons imported, by name

- **Unison**: content-addressed definitions, names as metadata — the real
  precedent for per-declaration hashing.
- **Coq** (`vos`/`vok`/`vo`): the tier split, and the visibility scar.
- **Lean**: `.olean` trust model (rung 1's shape); intra-file parallelism
  as confirmation of body-opacity.
- **rustc/Salsa**: red-green invalidation (compare outputs before
  invalidating downstream).
- **Zig**: hash semantic inputs not text; go daemon-resident. Their
  architecture doesn't transfer (no conversion, no open terms).

## What it assumes from elsewhere

- **[[elaboration-determinism]]** owns determinism as an enforced
  guarantee. Assumed here: only that elaborated output is a stable
  function of source + context, so interface hashes are well-defined. This
  is the hard prerequisite for the whole DAG.
- **[[context-representation-clones]]** owns the context representation.
  Assumed here: only that a shared-spine/persistent Ψ makes O(1) forking
  possible.
- **[[ai-facing-tooling]]** owns failures-return-search-state. Assumed
  here: only that the search-state format, when it exists, is the same one
  replay traces serialize.
- **[[prog-extension-lemma]]** owns the IR linking lemma. Assumed here:
  nothing yet — named as the shape precedent for Ψ-weakening as a
  build-system soundness theorem.
- **[[compile-typeclass-design]]** owns intensional instance keying
  (`.code`). Assumed here: only that one hashing scheme can serve both it
  and the cache DAG.

## Sequencing

Nothing blocks on the bootstrap. The spine: [[elaboration-determinism]] →
declaration-level interface hashing → daemon with shared-spine Ψ (joint
with [[context-representation-clones]]) → `quickcheck` tier → replay traces
(joint with [[ai-facing-tooling]]) → the verified-invalidation theorem.
Each stage is independently useful; the first two pay off single-session.

## Log

- 2026-08-06: Filed from discussion. Certificate replay agreed as the
  direction to design for directly (trace hook reserved from v1); the
  kernel-vs-elaborator ratio caveat recorded the same day.
