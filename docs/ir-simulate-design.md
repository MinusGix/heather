# FunctionIR and `simulate`: design sketch

Status: **design sketch, pre-implementation** (2026-07-31). Written before
the code, per repo discipline; when the implementing round lands, this file
becomes the specification it is checked against.

Tracking issue: `issues/ir-simulate-design.md`. Adjacent decisions live
where they are owned: the `Compile` class in
`issues/compile-typeclass-design.md`, the representation boundary in
`issues/datarepr-separation.md`, partiality/effects futures in
`issues/effects-direction.md`.

The design principle, stated once: **the IR is a proof object first and a
compiler artifact second.** Every representation choice below is scored on
what it costs the theorems — `equiv` certificates, pass-correctness lemmas,
version/lowering refinements — not on what it costs an eventual code
generator. Datarepr owns what runs; nothing here does.

---

## 1. Role, and the constraints it inherits

`FunctionIR` + `simulate` is the load-bearing spec object of certifying
compilation: a `Compile` instance couples IR production with an `equiv`
theorem that the IR simulates to the same result as the kerneltime
function, and custom passes, context-specific specialization
(`docs/sketches/surface-v3.md` §1), and eventual CPU-model refinement all
prove against `simulate`. Constraints already settled elsewhere and
inherited here:

- **Spec object, not runtime object** (`issues/datarepr-separation.md`):
  term size and reduction cost of the *encoding* are off the ledger. What
  stays on the ledger is the cost of *discharging `equiv` by conversion* —
  the kernel runs `simulate` — which is why this round owes a bench fixture
  (§11).
- **First-order data throughout.** The compiler keys on syntax: instances
  are intensionally keyed, artifact dedup keys on
  `(function syntax, ctx descriptor)`, `translate`/lowering is structural
  recursion, passes compare and rewrite subterms. All of it wants decidable,
  stable syntactic equality of IRs — so no function-valued fields (HOAS
  regions), independent of whether the kernel ever grows them. This is not
  a workaround for a missing feature; it is load-bearing for the design.
  (No specific `Compile` sketch is binding yet, but decidable IR equality
  is wanted under every candidate.)
- **The proof language is structural recursion** with IH = self-call
  (`match-recursion`). The IR's shape should make `simulate` structural,
  so that induction on a term *is* induction on its proof.
- **Result-typed partiality**: `simulate` handles divergence and stuckness
  explicitly (issue decision); fuel/step-indexing now, richer semantics
  later behind a stable interface (§6, §7).

## 2. Decision: term-form RVSDG

Two decisions folded together, argued separately.

**Structured over flat (SSA/CFG).** Against a CFG, `simulate` is a step
machine with a program counter; every loop proof becomes an invariant over
a transition relation — simulation diagrams, the heaviest proof style in
the CompCert tradition. With RVSDG-style regions, control flow exists only
as structured nodes: a conditional is a `gamma`, a loop is a `theta`, and
`simulate` of a node is defined from `simulate` of its sub-regions. Pass
correctness becomes local lemmas plus congruence — loop-invariant motion is
a statement about one `theta`, not a global diagram. Certificates compose
along the IR's own algebra (`simulate` of a composite in terms of
`simulate` of parts), which is what per-instance `equiv` proofs composing
over a call graph, and refinements composing over lowerings, both need. A
flat SSA level may exist *later, below* this one (§8): `Compile` is the
entrypoint and targets the structured level; lowerings are certified
translations.

**Term over graph.** RVSDG in the literature is a graph — multi-port nodes,
edge lists, acyclicity as a maintained invariant. Transcribed literally
into an inductive, well-formedness is a large extrinsic predicate and
`simulate` needs a topological traversal before it can begin; the round
would be spent on scheduling lemmas, not semantics. Instead: **let-normal
form**. A region is an ordered sequence of node bindings; each node refers
to region arguments and *earlier* results by environment index; structured
nodes carry sub-regions as fields. Acyclicity holds by construction, and
`simulate` is a left-to-right fold carrying an environment. This is
RVSDG's essential content — the graph view is how passes may *think*, and
a builder API can present it; the datatype is the tree.

## 3. The datatype (v1)

Sketch, in surface syntax that exists today (names indicative):

```heather
// A reference is an index into the current environment:
// region arguments first, then each node's output slots in order.
// Raw Nat, not Fin — see §8 for the deliberate staging.
type Ref = Nat

struct Region {
    args:    Nat,           // number of argument slots
    nodes:   [Node; n],     // dependency order; node i sees args + outputs of nodes < i
    results: List(Ref),     // the region's output slots
}

enum Node {
    Con(tag: Nat, fields: List(Ref)),      // build a value; binds 1 slot
    Gamma(scrut: Ref, arms: List(Region)), // match: arm k runs when scrut's tag is k,
                                           //   its fields bound as the arm's args;
                                           //   binds r slots (shared arm result arity)
    Theta(init: List(Ref), body: Region),  // loop: body takes n carried slots, returns
                                           //   1 + n (continue-flag, next state);
                                           //   binds n slots (final state)
    Apply(callee: Nat, args: List(Ref)),   // call by index into the Program;
                                           //   binds callee's result arity
}

struct Function { params: Nat, body: Region }
struct Program  { funcs: [Function; k] }
```

Points of note:

- **Multi-output lives in the binding form, not the value domain.** A node
  has an output arity and binds that many *consecutive environment slots*;
  `simulate` appends a vector of results. No tuple value exists: `Gamma`
  arms return an agreed arity, `Theta` carries n slots in and out,
  references are unchanged (they point at slots; a two-output node simply
  contributed two). This kills the projection-after-every-lookup noise and
  the arity-quantified lemmas that tuple values force, and it scales: in
  the intrinsically typed target (§8), "k slots" becomes "a telescope".
  Named ports are presentation — printer and builder API carry names, the
  datatype carries arities.
- **`Gamma` is `match`.** The data model is constructor trees (§4), so the
  conditional *is* case analysis on a constructor tag, with fields bound as
  arm arguments. No separate boolean/predicate machinery; a two-armed gamma
  on a `Bool`-shaped value is the ordinary conditional.
- **Recursion is `Apply` + fuel**, mutual recursion included (any function
  may `Apply` any index). No `phi`/fixpoint node in v1.
- **No primitive-op node yet.** `Con` + `Gamma` + `Theta` + `Apply` compute
  anything the spec level needs (a `Nat` add is a theta or a recursive
  apply — off-ledger by datarepr). A `Prim` alphabet is a v2 question tied
  to datarepr's choices, recorded in §12; adding a constructor to `Node`
  later is cheap, removing one is not.

## 4. The value domain

`simulate` needs values to flow through the environment, and `equiv` needs
to compare them with kerneltime results. v1: **constructor trees**,

```heather
struct Val { tag: Nat, fields: List(Val) }
```

— first-order data generic over every spec inductive (this is the
`Rose`-shaped nesting `container-fields` proved out). Each spec type gets
an embedding, mechanical and eventually generator-derived
(`issues/generators-in-the-language.md`):

```heather
fn embed_nat(n: Nat) -> Val { ... }   // Zero ↦ {0, []}, Succ m ↦ {1, [embed m]}
```

and `equiv` is stated *through* the embedding (§6): the IR computes the
embedded result of the function on embedded arguments. The embedding is
per-type and injective; injectivity lemmas are part of the stdlib
co-development bill (§10). What `Val` is **not**: it is not datarepr's
runtime representation (that boundary is certified separately, and later),
and it is not typed — a `Gamma` scrutinizing a tag out of range is `Stuck`,
not ill-formed (§5).

## 5. `simulate`

```heather
enum Res { Out(vals: List(Val)), OutOfFuel, Stuck }

fn simulate(p: Program, f: Nat, args: List(Val), fuel: Nat) -> Res
```

via a region evaluator folding nodes left-to-right over an environment
`List(Val)`:

- `Con`: look up fields, append one slot. `Gamma`: scrutinize the tag,
  run the selected arm's region on the fields, append its results; a tag
  with no arm, or a reference out of range, is `Stuck`.
- `Theta`: run the body on the carried slots; result slot 0 is the
  continue-flag (tag 0 = stop, tag 1 = continue); iterate. **Fuel is spent
  here and at `Apply`, nowhere else** — `simulate` is structural on the IR
  everywhere but the two constructs that repeat, so proofs about
  loop-free, call-free fragments never mention fuel at all.
- `Stuck` is explicit, total, and *boring by design*: scoping and arity
  discipline is extrinsic (§8), so a junk reference simulates to `Stuck`
  and "this IR never sticks" is an ordinary theorem — which `equiv`
  subsumes, since `Out(...) ≠ Stuck`. Well-formedness buys no soundness in
  this architecture (the kernel re-checks everything; a bad IR is one whose
  certificate won't discharge), so it is not paid for intrinsically in v1.

**Cost model note** (issue log, 2026-07-28): with payload-copying
substitution fixed, check — measure, not assume — that fuel-indexed
evaluation is linear in fuel under conversion. The environment fold does
O(ref) lookups per node; that is fine for a spec object, but the bench
fixture (§11) is where the claim is tested at realistic size.

## 6. The fuel interface: `converges`

Raw fuel appears in `simulate`'s definition and **nowhere else**. The
stated interface, defined once:

```heather
// The ∃-closure — the Delay monad's ⇓, built over fuel.
def converges(p, f, args, vs) := exists n. simulate(p, f, args, n) == Out(vs)

theorem fuel_monotone(...):     // proved once, generically
    simulate(p, f, args, n) == Out(vs) -> n <= m ->
    simulate(p, f, args, m) == Out(vs)
```

- **`equiv` is stated via `converges`** (through the §4 embedding):
  a `Compile` instance proves, for all spec arguments `x`,
  `converges(p, f, [embed(x)], [embed(fun(x))])`.
- **`refines` is stated via `converges`**: IR₂ refines IR₁ iff every
  convergence of IR₁ is a convergence of IR₂. Transitive by construction —
  no fuel-bound arithmetic leaks into refinement chains — so lowering
  certificates and version-bump certificates compose, which is the stress
  test the tracking issue demands of `simulate`'s type.
- **Discharge uses computed bounds.** The existential's witness is a
  kerneltime `fuelbound(args)`; proving the instance is *running the
  interpreter* at that bound and letting conversion close the equation,
  with `fuel_monotone` bridging discharge to the stated form. This is the
  thesis-shaped fixture of §11.

The interface is deliberately opaque about how divergence is modeled:
clients see `converges`/`refines`/`fuel_monotone`, so if the kernel later
grows a richer partiality story — coinductive Delay, guarded recursion /
the later modality, Bove–Capretta domains (which want function-typed
fields) — `simulate` migrates behind the same relation. Those futures are
**documented and owned by `issues/effects-direction.md`**, not gates here.

## 7. Effects: state slots, later

RVSDG threads effects as state edges, and that is exactly
`effects-direction`'s current leaning (uniqueness threading): a capability
is a value in an environment slot, `simulate` stays pure, `equiv` stays
propositional equality. v1 defines **no** effectful nodes; the design
constraint honored now is only that nothing above precludes state-carrying
slots — and nothing does, since slots are the one structure everything
already flows through. Trace-shaped `simulate` (interaction trees) would
arrive, if ever, behind §6's interface.

## 8. The eventual target: intrinsically typed syntax

The staging ladder, recorded so v1's choices read as staging, not belief:

1. **v1 (this sketch): extrinsic.** `Ref = Nat`, `Stuck` explicit,
   well-scopedness an ordinary predicate when a pass wants it. Route 1 of
   `docs/inductive-indexed-lowering.md` — extrinsic judgments over declared
   syntax — is measured and green (§8.2 prototype).
2. **Target: intrinsically scoped, then typed.** Scope-indexed nodes
   (`Fin`-refs) delete the scoping junk; type-and-context-indexed IR
   (`IR(Γ, τ)` with `simulate : Env(Γ) -> Fuel -> Res(τ)`) deletes `Stuck`
   entirely and narrows `Res` to `Out | OutOfFuel`. Every pass is
   scope/type-preserving by construction rather than by per-pass lemma.
   The gate is real: index arithmetic under passes means transports along
   `Nat`/context equations, stuck at neutral indices — the fording problem
   — so this **wants SProp** (`issues/sprop-strict-prop.md`, route 2b) and
   should be prototyped against it, per the indexed-families resolution.
3. **Migration.** We own the language wholly and this precedes any public
   release, so the likely path is simply *rebuilding* the IR intrinsically
   when SProp lands, not maintaining v1 alongside. The versioned-namespace
   + `translate`-with-certificate machinery (tracking issue) remains
   designed — it is the same mechanism a public-era version bump or an SSA
   lowering needs, and exercising it once on v1→v2 is cheap insurance —
   but it is a tool available, not a promise of eternal v1 support.
   One flag for that boundary, recorded now so it isn't rediscovered:
   intrinsic terms carry more syntax (coercions), so intensional instance
   keying and artifact dedup need re-examination when the move happens.

## 9. Deliberately rejected, each with its reason

| Rejected | Why |
| --- | --- |
| Graph representation (nodes + edge lists) | well-formedness becomes a scheduling theory; term form gets acyclicity by construction (§2) |
| Flat SSA/ANF as *the* spec IR | step-machine semantics ⇒ simulation-diagram proofs; also already ruled out of a prior decision's ledger (`branching-inductives-choice.md` §3) |
| HOAS / function-valued region fields | destroys decidable syntactic IR equality, which intensional keying and dedup are built on (§1) — rejected on merits, not on kernel capability |
| Tuple values for multi-output | projection noise + arity-quantified lemmas; multi-slot binding subsumes it (§3) |
| Intrinsic scoping/typing in v1 | buys no soundness here, and without SProp the transport tax lands at neutral indices (§8); it is the *target*, staged |
| `Prim` op node in v1 | alphabet choice is datarepr-entangled; `Con/Gamma/Theta/Apply` are complete for spec purposes; additive later (§3) |
| Delay monad / later modality / Bove–Capretta now | coinduction is out of kernel v0; guarded recursion is a metatheory round; domains want function fields — all owned by `effects-direction` as futures behind §6's interface |
| Raw fuel in any public statement | `converges` + `fuel_monotone` is the interface; fuel is `simulate`'s private argument (§6) |

## 10. Stdlib co-development

The first round that writes substantial Heather libraries rather than test
snippets; expected bill, filed as issues as gaps surface rather than
pre-built: `Res`/`Option`-shaped enums and their lemmas, `List` operations
(`nth`, `append`, length lemmas) used by the evaluator, the `embed_T`
family and injectivity, `fuel_monotone` and the small bound-combinator
kit, and — flagged by its own issue as this round's likely first bite —
`map-tabulate-convergence`, to be decided against this consumer (its
option 2, one normal form, is the removal rather than the paper-over).

## 11. Acceptance sketch (for the implementing round)

1. `Val`, `Ref`, `Region`, `Node`, `Function`, `Program`, `Res` declared in
   Heather; `simulate` an ordinary kerneltime function; `heather check`
   green on the file.
2. A hand-written IR for a small recursive function (e.g. addition via
   `Apply`, or a `Theta` counting loop) simulates to the embedded expected
   result *by conversion* at literal fuel.
3. `fuel_monotone` proved; `converges` and `refines` stated; refinement
   composes across two hand-written IRs for the same function (the §6
   stress test, small).
4. A hand-written `equiv`-shaped theorem for one function, discharged at a
   computed bound — the first end-to-end certificate, ahead of any
   `Compile` class machinery.
5. The bench fixture: conversion discharging `simulate ir fuel` at
   realistic program size and fuel, into
   `crates/kernel/benches/kernel/fixtures/` (~30-line family, per the
   kernel-benchmarks round), with the linearity-in-fuel claim measured.
6. Negative controls: a junk reference simulates to `Stuck`; an
   insufficient literal fuel yields `OutOfFuel`; a wrong-result IR's
   `equiv` statement is refuted or fails to check. (Per
   `docs/testing-generated-terms.md` discipline: vary neutral scrutinee
   and checking position where the schemas allow.)

## 12. Open questions (design)

- **`Prim` alphabet and its datarepr interplay** (§3): when runtime
  representations exist, do primitive ops enter the IR (with per-op
  `simulate` clauses certified against spec functions), or stay below the
  lowering boundary?
- **`CallCtx` descriptor shape** for context-specific instances
  (`surface-v3.md` §1) — adjacent to this design; the lever is keeping the
  descriptor coarse. Untouched by v1; recorded so it stays reachable.
- **Result arity of `Apply`**: v1 can fix every `Function` at result
  arity 1 (kerneltime functions return one value) and let `Gamma`/`Theta`
  be the only multi-slot binders; decide when writing the evaluator,
  whichever makes the fold's invariant cleaner.
- **Where embeddings live** once `generators-in-the-language` moves the
  derived-artifact story into the meta layer — `embed_T` is exactly such
  an artifact.

## 13. Implementation notes (v1 as landed — `lib/ir_v1.hthr`, 2026-07-31)

The implementing round (§11 items 1, 2, 6) landed the same day the sketch
did, and reality edited the sketch in five places. None of them changes a
§2–§8 decision; each is recorded here with its reason so the next reader
doesn't re-derive it.

1. **Chains, not vectors.** §3 sketched `[Node; n]` container fields and
   `List(Ref)`; the landed datatype uses cons-chains throughout — `Refs`
   for argument lists, `Arm`-cells inside `Ir` for gamma's arm list,
   `Prog` as a chain of bodies, and one `Val` inductive that doubles as
   value and value-list (an environment is a `VCons`-chain; so is a
   `VCon`'s field list, so junk is representable and answered by `Stuck`).
   Reason: an interpreter consumes sequences *statefully*, which structural
   recursion over a chain gives directly, while vectors would drag in
   `nth`/`Fin` machinery and the `map`/`tabulate` seam for zero payoff at
   the spec level. A side effect: the map–tabulate hazard flagged in §10
   never materialized in v1.
2. **The termination discipline shapes signatures.** A recursive `fn` must
   pass every non-decreasing parameter *unchanged* (the match-recursion
   MVP; generalizing a varying argument into the motive is that issue's
   one deferred case). Where two arguments vary together, the varying one
   moves into a returned function: `lookup(env) : Nat -> OptVal`,
   `pick_arm(arms) : Nat -> Ir`, `find_fun(prog) : Nat -> Ir`, and `eval`
   itself recurses on fuel alone, returning `Val -> Ir -> Res`.
3. **Fuel is a step count, not a theta/apply count.** §5's "fuel spent
   only at the constructs that repeat" needs lexicographic descent
   (fuel, ir), which the checker doesn't do; v1 spends one fuel per
   instruction. Private to `simulate` either way — `converges` (§6) is
   deliberately insensitive to the accounting. Corollary that matters in
   practice: *unused* fuel is free at conversion time (only taken steps
   unfold), so fuel constants in theorems are generous rather than exact.
4. **One ih occurrence, by measurement.** Every syntactic occurrence of
   the self-call in a recursive body costs ~50ms per executed step at
   conversion, because `fn`s are inlined at every use and the ih term
   carries the whole eliminator. `eval` therefore dispatches through a
   single `step(ev, prog, env, ir)` with the recursive call passed once as
   a value. The full numbers and the two compounding causes live in
   `issues/simulate-conversion-cost.md` — which is this design's §5
   cost-model warning confirmed, and now the bench fixture's real subject:
   at ~2s per executed step, "realistic program size and fuel" (§11
   item 5) measures that issue until it moves.
5. **Scoping is mixed, deliberately.** `LetMatch` arms are lexical (fields
   prepended to the enclosing environment); `LetLoop` bodies and called
   functions are closed (carried slots / arguments only). Closed loop
   bodies are what lets iteration re-enter through the internal `LoopIter`
   form without environment surgery; lexical arms avoid threading every
   outer slot through every gamma. References are de-Bruijn-style
   *distances* (0 = most recent), not §3's absolute indices — the natural
   reading against a cons environment.

**Deferred to the next round, with the route sketched:** §11 items 3–4
(`converges`, `fuel_monotone`, `refines`, a ∀-args `equiv`). Two real
blockers, both now measured rather than guessed: `fuel_monotone` is an
IH-generalizing induction (the motive must quantify `env`/`ir`), which is
match-recursion's known deferred case — the manual route exists via an
explicit motive (`match fuel as λ f => (env: Val) -> …` with the
`Succ(k, ih)` arm spelling) and is a session-sized proof through `step`'s
case tree; and stating `converges` wants either Σ at the statement level
or the computed-bound form. Neither blocks using the interpreter, which is
why items 1/2/6 shipped first.
