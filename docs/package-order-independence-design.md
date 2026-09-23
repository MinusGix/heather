# Order-independent declarations within a package

**Status: proposal (2026-09-22), not decided.** Written after the `std`
namespacing refactor hit the import-order wall: `nat.hthr` cannot state
`instance Cmp<Nat>` beside the kit that fills it, nor use `List`, because
`algebra` and `list` import `nat`. Issue: `issues/package-order-independence.md`.
The small, independent fix for the name clash that started the conversation is
`issues/receiver-dispatch-coinciding-readings.md`; nothing here depends on it.

## 1. The goal, and the scope

Within a **package** (`lib/std` is one), neither the order of declarations in
a file nor the order of files matters: any declaration may refer to any other,
and imports are about **visibility and namespacing only**. Between packages the
graph stays acyclic, as in Rust (items order-free inside a crate, crates a DAG).

In-file and cross-file order independence are **one design**: under the
mechanism below, a package elaborates as one large file with namespaces. Doing
in-file first and cross-file later would build the machinery twice.

Non-goal: cyclic *packages*. Cycles between compilation units with separate
interfaces are where GHC's `hs-boot` files and ML recursive modules went; the
cycles worth having are between declarations.

## 2. What already holds

- **The kernel does not change.** Ψ stays one ordered telescope. Order
  independence is a frontend property: the frontend discovers an order and
  hands the kernel a telescope, each strongly connected component emitted as
  a group, exactly as a mutual group is emitted today
  (`docs/mutual-recursion-design.md` §2). The kernel stays un-fancy.
- **Name meaning is already order-free.** `docs/modules-design.md` §4 never
  lets import order shadow: a name visible from two places is ambiguous at
  use. Widening visibility to the whole package therefore changes the reading
  of no name that resolved before; at worst it turns a resolution into an
  ambiguity error, which is the growth invariant working.
- **Scheduling determinism has precedent.** The deferred kernel gate
  (`docs/parallel-kernel-gate-design.md`) already reports and records in
  submission order regardless of worker completion order. The same discipline
  applies to Ψ order here (§6).

## 3. Why a syntactic sort is not enough

Dependencies are **type-directed**. `n.le_dec(m)` resolves through the type of
`n`; instance resolution, designations (`+ at Nat`), carrier-directed numerals
and receiver dispatch all pick their target from inferred types. The set of
declarations a body depends on is known only after it is elaborated.

A syntactic over-approximation — every declaration any mention *could*
resolve to — gives a sound order, but it fuses unrelated kits through shared
member names (every `.le_dec` depends on every `le_dec`) into false SCCs.
That costs the two things this is for: per-declaration caching and parallelism.
It is acceptable only as a fallback, never the design.

The principled route is **demand-driven elaboration**: elaborating X asks for
Y's signature, and Y's signature is elaborated then, if it is not yet.
Dependencies are recorded as they are demanded; cycles are detected on the
demand stack.

## 4. Two queries per declaration, and the cycles between them

Each declaration has a **signature** query (its type, universe parameters,
registration as a name) and a **body** query (its definiens, elaborated and
gated). Dependent types blur the line: a signature can need a body to compute
(a type mentioning `n + 1` needs `add` to reduce), so a signature query may
demand another declaration's body query.

The demand stack classifies every cycle:

| cycle | meaning | outcome |
|---|---|---|
| body(X) → sig(Y) → … → body(X)'s own sig only | ordinary forward reference | fine: sigs first, bodies after |
| body(X) → body(Y) → body(X), via δ in a *checking* step | mutual recursion | a group: the existing lowering, §5 |
| sig(X) → body(Y) → … → sig(X) | a type that needs its own definition | error, naming the chain |
| sig(X) → sig(Y) → sig(X) | mutually dependent signatures | error for now (induction-recursion is out of scope) |

The error rows need messages that print the demand chain with spans; that is
the diagnostic cost of the feature, and it is paid once, here.

Open question: whether any theorem body is ever demanded by another query
(δ-unfolded during elaboration or checking). If none is, theorem bodies are
**leaves** of the demand graph, which §7 relies on.

## 5. Mutual recursion loses its tiebreak

`docs/mutual-recursion-design.md` forms groups from **adjacency** and ranks
same-measure calls by **declaration order** (§ "the rank is declaration order,
first-declared highest"). Order independence removes both inputs:

- Groups become SCCs of body queries. Adjacency stops mattering.
- The rank needs a new source. Candidates: an explicit rank annotation; the
  topological order of same-measure edges, with a cycle among them an error
  asking for a strictly decreasing measure; or keeping source order *within
  one file* as a tiebreak — which reintroduces order sensitivity through the
  back door and is probably wrong.

This is the one existing design this proposal amends; decide it in the design
pass, not the implementation.

## 6. Instances, visibility, and the canonical Ψ order

**Instance heads before bodies.** Resolution consults the registry, so every
instance head (`Cmp<Nat>`, `Monoid<List<A>>(List::append)`) in the package
must be registered before any query that resolves. Heads are therefore
elaborated in a first phase and may not themselves need instance resolution —
a mild restriction, to be checked against `lib/std` before it is written down.
Instance *bodies* are ordinary body queries.

**Visibility.** Each file still has its own scope: what it imports decides
what it can *name*, unqualified or qualified, exactly as today. What changes is
that the importee's declarations no longer have to be elaborated first. An
import between files in one package may form a cycle; between packages it may
not.

**Canonical Ψ order.** The emitted telescope is a deterministic function of
the source, never of scheduling: topological order of the SCC DAG, ties broken
by (file canonical path, source position). The kernel-visible order of a
package is then stable across widths, runs and machines, which the verdict
store and `--timings` diffs both need.

## 7. Parallelism, staged

The declaration graph exposes far more parallelism than the file graph
(Lean's critical path is its import DAG). The engineering bill is the
elaborator: its state is one `&mut` session, so parallel queries need either a
frozen committed prefix per worker or a sharded, query-keyed state.

Staged so each step is useful alone:

1. **Serial demand-driven elaboration** — order independence, no new
   parallelism. The existing deferred kernel gate keeps checking in parallel
   behind it.
2. **Parallel leaf bodies** — theorem bodies (if §4's open question comes back
   "leaves") elaborated on workers over the committed signature world. In a
   proof library that is most of the work; Coq's asynchronous proofs and
   Lean 4's parallel proof elaboration are this step.
3. **Parallel queries in general** — only if step 2's profile says the
   signature spine is the bottleneck.

## 8. Caching

Semantic module images compose in loader order, keyed by an ordered vector of
dependency interface hashes (`docs/semantic-module-images-design.md`). Cyclic
files break "compose in loader order". The natural replacement is the
declaration-level record the verdict store and slice replay already point at
(`issues/declaration-slice-replay.md`): key each declaration's result on its
own source and the interface hashes of what it **demanded** — the recorded
dependency set, not the file's imports. An edit then invalidates the
declarations that demanded what changed, not the files downstream of it.

Whether module images survive as a packaging of per-declaration results, or
the image becomes per-SCC, is for the design pass.

## 9. Prior work

From memory; verify before quoting.

- **Rust**: order-free items and mutually referencing modules inside a crate,
  acyclic crates. Name resolution is a fixpoint over imports before type
  checking. The scope split proposed here.
- **Olle Fredriksson's Sixten / Sixty, with the Rock library**: a dependently
  typed language with query-based, incremental, parallel elaboration and
  order-free top-level declarations. Closest in spirit; see his
  "Query-based compiler architectures" (2020).
- **Salsa / rust-analyzer**: the mature query model. It also serves the LSP,
  which wants per-declaration invalidation anyway.
- **Coq asynchronous proof processing** (Barras, Tankink, Tassi, ITP 2015) and
  **Lean 4 parallel proof elaboration**: §7 step 2 on its own.
- **Agda**: forward declarations and `interleaved mutual` blocks — a halfway
  point that keeps the programmer responsible for order.
- **Cautionary**: GHC `hs-boot` (cyclic modules through hand-written
  interfaces) and ML recursive modules (a hard typing problem). Both make
  cycles between *units* the feature.
- **Unison**: content-addressed definitions, no files at all — the far end of
  the same axis, useful for the caching story in §8.

## 10. Open questions for the design pass

1. Are theorem bodies leaves (§4)?
2. The mutual-recursion rank (§5).
3. Do all `lib/std` instance heads elaborate without resolution (§6)?
4. Error recovery: a failed signature query poisons its dependents; today's
   recovery discipline is "check against whatever landed", which needs a
   demand-graph restatement.
5. Where the elaborator's session state splits into per-query and shared
   (§7), and what that costs the serial path.
6. What happens to `with_prelude` and the prelude's implicit import: part of
   the package graph, or its own package below `std`.
