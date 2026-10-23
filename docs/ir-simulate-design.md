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
   stress test, small). *Done 2026-07-31, with the statement shapes
   amended — see note 7.* `fuel_monotone` in both the `+ k` and the `<=`
   shape; `refines` bounded, with `refines_refl`/`refines_trans` and a
   three-link concrete chain (the add loop, a `LetCall` to it, a `LetCall`
   to that) composing at `plus2 ∘ plus2`. **The full stress test —
   two *semantically different* IRs — landed 2026-08-01**
   (`issues/cross-ir-refinement.md`): `add_rec_body`/`add_rec_prog` is `add`
   by recursive `Apply` (non-tail, bound `2a + 2` against the loop's `a + 5`),
   `add_rec_runs` is its invariant over an arbitrary environment tail, and
   `loop_refines_rec`/`rec_refines_loop` relate the two IRs in both
   directions. Two findings are recorded in note 8.
4. A hand-written `equiv`-shaped theorem for one function, discharged at a
   computed bound — the first end-to-end certificate, ahead of any
   `Compile` class machinery. *Done 2026-07-31:* `add_equiv` is ∀-arguments
   (`add_loop_runs` is the loop invariant, `bumps_embed` the embedding
   lemma) at the computed bound `add(a, 5)`, `add_equiv_at` is the same at
   any larger fuel via `fuel_monotone`, and `add_equiv_through_calls`
   transports it along the refinement chain.
5. The bench fixture: conversion discharging `simulate ir fuel` at
   realistic program size and fuel, into
   `crates/kernel/benches/kernel/fixtures/` (~30-line family, per the
   kernel-benchmarks round), with the linearity-in-fuel claim measured.
   *Done as `conv/simulate-payload` and `conv/simulate-depth`; re-aimed at
   a depth-of-nesting family when the exponent was diagnosed;* **retired
   2026-07-31** — see note 6's second amendment. The nesting axis was never
   reproducible as a kernel bench (four hand-built families tried,
   `docs/nbe-conversion-design.md` §12), its instrument is
   `scripts/probe-whnf-sharing` at the CLI, and its subject no longer
   exists.
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

## 13. Implementation notes (v1 as landed — `lib/certgen/ir_v1.hthr`, 2026-07-31)

The implementing round (§11 items 1, 2, 6) landed the same day the sketch
did, and reality edited the sketch in five places; note 6 is a later
amendment from the same day. None of them changes a §2–§8 decision; each is
recorded here with its reason so the next reader doesn't re-derive it.

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
4. **One ih occurrence, by measurement — a cliff then, a constant now.**
   *Measured 2026-07-31 against term-rewriting conversion:* every syntactic
   occurrence of the self-call in a recursive body cost ~50ms per executed
   step, because `fn`s are inlined at every use and the ih term carries the
   whole eliminator; 0.24s at one occurrence became 13.7s at ~10. `eval`
   therefore dispatches through a single `step(ev, prog, env, ir)` with the
   recursive call passed once as a value. *Re-measured the same day against
   the value domain* (`issues/nbe-conversion-round.md`): six occurrences
   instead of one costs **1.24×** on the whole library file. The multiplier
   is gone — a duplicated occurrence now evaluates to a shared value rather
   than a copied term — so the discipline survives as good style and not as
   a constraint. Keep it in `lib/certgen/ir_v1.hthr` (restructuring the library to
   exploit the change is a round of its own); stop *requiring* it of new
   Heather code. The original numbers and the two compounding causes are in
   `issues/simulate-conversion-cost.md`.
5. **Scoping is mixed, deliberately.** `LetMatch` arms are lexical (fields
   prepended to the enclosing environment); `LetLoop` bodies and called
   functions are closed (carried slots / arguments only). Closed loop
   bodies are what lets iteration re-enter through the internal `LoopIter`
   form without environment surgery; lexical arms avoid threading every
   outer slot through every gamma. References are de-Bruijn-style
   *distances* (0 = most recent), not §3's absolute indices — the natural
   reading against a cons environment.

6. **The interpreter stays recursive, and that is now a decision rather
   than a default** (amendment, 2026-07-31, second round of the day). The
   §5 cost-model note asked whether fuel-indexed evaluation is linear under
   conversion. It is not: `simulate` is *exponential*, ~×22 per add-loop
   iteration, and `issues/whnf-sharing-term-growth.md` owns the mechanism.
   The natural response — replace the recursive evaluator with a
   defunctionalized step machine (configuration = environment ×
   instruction × continuation frames, `step : Config -> Config`, `run`
   iterating on fuel in tail position), so that nothing recurses in
   scrutinee position — was **implemented and measured strictly worse**:
   flat cases stayed flat, but every sub-region *return* became
   exponential, so an 8-deep chain of `LetCall`s (0.76s / 10 MB recursive)
   died at an 8 GB cap. The isolating experiment is in that issue: swapping
   one configuration field for a semantic *identity* wrapper — same values,
   same steps — turns flat into ~×2 per level. The cost axis is not the
   shape of the recursion, it is whether a carried term is stored as an
   unforced redex, and no in-language restructuring reaches that: the
   language cannot force a value.

   Consequences for this design. §5's recursive definition is both the
   declarative reading *and* the implementation, and stays so. Fuel remains
   a step count and stays private behind §6. The §11 item 5 bench fixture
   is measuring the right object but the wrong axis, and owes a
   depth-of-nesting family (`docs/testing-generated-terms.md` axis 5). The
   real fix is a kernel that shares a forced result — NbE / a value domain,
   the issue's lever 1, which is a design round and not a performance one;
   **if it ever lands, nothing here has to change**, which is the argument
   for leaving `simulate` in its pretty form and paying the discipline
   instead: certificates keep non-tail nesting shallow, and tail chains are
   free.

   **It landed, and nothing here had to change** (amendment, 2026-07-31,
   `issues/nbe-conversion-round.md`). Conversion now evaluates into a value
   domain where an eliminator's β extends an environment instead of copying
   a branch, and `simulate` — unmodified, in its pretty form — went from
   exponential to flat: the arm-nested probe's N = 15 from 33.8s / 4544 MB
   to 1.45s / 20.9 MB, and `add(2,3)` through `LetCall` from 20.9s to
   ~0.05s. Both combined theorems are now in `lib/certgen/ir_v1.hthr` and the whole
   file checks in 1.25s at 14.4 MB. The bet that the fix belonged in the
   kernel and not in the interpreter's shape paid; the two consequences for
   *this* document are note 4's discipline (a constant now, not a cliff)
   and §11 item 5's re-aimed bench obligation, which is retired below.

7. **`converges` and `refines` are statement *shapes*, not definitions**
   (amendment, 2026-07-31, third round of the day — the round that landed
   §11 items 3–4). §6 defines `converges(p, f, args, vs) := exists n.
   simulate(…, n) == Out(vs)` and states `refines` through it. Neither is
   definable at the surface today, for two independent reasons, and both are
   recorded here rather than worked around silently:

   - **No `exists`.** The surface has no Σ over an arbitrary predicate: a
     `record` may carry dependent fields but takes only *type* parameters, so
     `Converges` cannot be indexed by `(p, env, ir, vs)` and an inhabitant of
     an un-indexed Σ proves nothing about a particular program. Declaring an
     indexed family would need surface syntax for one, which does not exist
     (`issues/indexed-families.md`, and §8's ladder puts it behind SProp
     anyway).
   - **No `->` in expression position.** A `fn` body is an expression, and
     the expression grammar has no function-type former, so even the
     ∀-shaped half of the interface cannot be given a *name*. It can be
     written in any *type* position, which is where theorem statements live.

   What landed instead, and why it is the same interface:

   - `converges` at a **computed bound** — `eval(bound(args), p)(env, ir) =
     Out(vs)` — which is what §6 already says discharge uses. The ∃-closure is
     the only part missing, and it is missing at the *statement* level only:
     every consumer this design has (a `Compile` instance, a refinement, a
     pass lemma) carries its bound anyway.
   - `refines` in the **bounded** form: IR₂ refines IR₁ at fuel map `b` when
     every convergence of IR₁ at `n` is a convergence of IR₂ at `b(n)`.
     §6's "transitive by construction" survives exactly — composition is
     composition of the bounds (`refines_trans` in the library, a one-liner)
     — and `fuel_monotone` is what keeps the shape robust, since a bound may
     always be loosened. The un-bounded ∃-form is the image of this one under
     the ∃-closure, so nothing has to be re-proved when Σ arrives.
   - `fuel_monotone` **verbatim**, with `n <= m` spelled `Le(n, m)`: the
     prelude has no order on `Nat` and no indexed families, so `<=` is
     *decided* in the library rather than declared — `Le` is a `fn`
     returning `Type` whose body is the reflection equation
     `leb(n)(m) = True`, and δ-unfolding makes the two interchangeable, so
     the boolean stays an implementation detail of the proposition rather
     than the way every ordering hypothesis is spelled. Its two absurd cases are
     then ordinary constructor equations, which `absurd` already refutes — no
     `Empty` and no large elimination. The `+ k` shape (`eval_mono_plus`) is
     proved first and is what the `<=` shape reduces to, via `le_add`.
     (**Amended 2026-08-16**: `Le`'s body is now a recursion into `Type` and
     the reflection equation is gone — `docs/nat-order-design.md`. The
     paragraph is kept as the record of why the reflection was chosen then.
     Nothing in this file changed with it: `fuel_monotone` and every other use
     here goes through the lemma kit, so all of `lib/certgen/ir_v1.hthr` checked
     unmodified across the swap, which is the evidence for the discipline that
     made the swap safe.)

   One surface change was needed and made: a **motive body is parsed with the
   type grammar**, so it may be a function type. An IH-generalizing motive is
   literally `λ z => (env: Val) -> … -> P(z)`, and without it §11 item 3 is
   not statable. Backwards compatible — the type grammar falls through to the
   expression grammar for equations, names and applications, which is every
   motive that parsed before (`crates/elab/tests/motives.rs`,
   `issues/ih-generalization.md`). `absurd`/`inj` also now δι-reduce both
   endpoints before reading constructors off them, because the base case of a
   fuel induction reaches its equation by *computing*.

   The cost, since `issues/ih-generalization.md` asked for it rather than an
   assumption: the file goes from 1.31s / 14.2 MB to 26.9s / 18.6 MB, and
   ~18s of that is `step_mono` alone. Note 4's "a duplicated ih is now free"
   does not extend to a generalized motive: the tax is term *size* at each
   arm of a case tree over the whole `Ir`, and it is large. Peak memory
   barely moved, so this is elaboration and conversion work on big terms, not
   the old copying blowup.

   **Amendment, 2026-08-01: the ∃-closure is now statable, and `converges` is
   written as §6 states it.** The first of the two reasons above is retired:
   `record` takes **value parameters** (`docs/surface-value-parameters.md`,
   `issues/surface-existential.md` route 1, no kernel change), so a record *is*
   indexable by `(p, env, ir, vs)` and

   ```heather
   record Converges(p: Prog, env: Val, ir: Ir, vs: Val) {
       n: Nat,
       h: eval(n, p)(env, ir) = Out(vs),
   }
   ```

   is the definition, bound genuinely hidden. `refines` in the ∃-shape then
   loses its fuel map entirely and composition becomes ordinary implication
   chaining (`refines_trans_conv`, no `b1`/`b2`). The bounded form **stays**,
   additive: `refines_of_bounded` is the ∃-closure proved rather than asserted,
   so this note's "nothing has to be re-proved when Σ arrives" is now a landed
   one-liner rather than a claim. `add_converges` /
   `add_converges_through_calls` are the certificate exported in the ∃-form —
   the shape a `Compile` instance wants, since a caller has no reason to know
   the bound.

   The second reason **survives**: `refines` still cannot be given a *name*,
   because a `fn` body is an expression and `->` is not one. That is
   `issues/type-definitions`', not this design's, and it blocks nothing —
   `refines` remains a statement shape written out at each use. (The
   investigation also found the note's parenthetical about a `fn` returning
   `Type<0>` to be only half true: an *equation* body works and `P(n)` in type
   position works; what fails is `->` in an expression body.)

   **Amendment, 2026-08-01 (same day, later round): the second reason is
   retired too, and note 7 is now fully spent.** `->` and dependent binder
   groups are expressions (`docs/types-as-expressions.md`,
   `issues/type-definitions.md` route 2 — no kernel change, no new declaration
   form), so a type-valued `fn` is an ordinary `fn` and

   ```heather
   fn Refines(p1: Prog, i1: Ir, p2: Prog, i2: Ir) -> Type {
       (env: Val) -> (vs: Val)
       -> Converges(p1, env, i1, vs) -> Converges(p2, env, i2, vs)
   }
   ```

   is the definition §6 asked for. `refines_refl_conv`, `refines_trans_conv`
   and `refines_of_bounded` in `lib/certgen/ir_v1.hthr` are now stated *through* the
   name rather than spelled out — the fuel-map-free ∃-shape is the one that
   got named, which is the right one: the bound is inside `Converges`, so
   `Refines` has exactly the four arguments the relation is about. The bounded
   form stays spelled out, since it is `refines_of_bounded`'s hypothesis and
   naming it would abbreviate one use.

   The cost went the other way from the guess: the file is **35.96s → 32.90s**
   release (−8.5%), because the statement is elaborated once instead of six
   times and conversion compares a δ-stuck head instead of the shape it
   unfolds to. Recorded on `issues/schema-construction-caching.md`.

   A second consumer landed with it: `BindInv`, the inversion record for
   `k_bind` (`k_bind(ev, env, rest, r) = Out(vs) -> ∃ ws. r = Out(ws) × …`),
   proved once and consumed by `let { ws, hr, hk } = …`. It **retires three of
   `step_mono`'s four convoy motives**, a measured 38.5s → 33.7s on the file
   (release, everything else held identical): −12.6%. The fourth (`LoopIter`,
   which scrutinizes through `k_iter` rather than `k_bind`) keeps the remember
   idiom. Net for the round the file is 27.5s → 33.7s, the increase being the
   new surface itself — two records and nine theorems — and not the rewrite.

8. **A refinement between two different programs is stated on a *family* of
   environments, not on all of them** (2026-08-01, the cross-IR round). §6 says
   "IR₂ refines IR₁ iff every convergence of IR₁ is a convergence of IR₂", and
   `Refines` says it with `(env: Val)` quantified over every value. Between the
   theta-loop `add` and the recursive-`Apply` `add` that statement is **false**,
   and `no_full_refines` in the library derives `0 = 1` from an inhabitant of
   it. The witness is an environment whose first slot is a tag-1 node whose
   field is a tag-0 node that itself carries a field: neither IR sticks (the
   extra field only shifts the lexical arm environment), and they answer
   differently, because the loop threads its accumulator *through the carried
   slots* — where a junk field displaces it — while the recursion wraps its
   `Succ` around the callee's answer on the way out, where nothing can. So
   `RefinesNat2` carries the family's binders (`a`, `b` embedded, an arbitrary
   environment tail) in place of `Refines`'s `env`. This is not a weakening of
   §6: it is the observation that a certificate relates two IRs *on the calling
   convention it is about* — the same convention `CompileNat2` already fixes —
   and that well-formedness, deliberately extrinsic (§5), is exactly what the
   family binders re-supply where a relation needs it. The clean general form,
   `RefinesOn(dom: Val -> Type, …)`, is what the library now states — a record
   type applied to its value parameters IS a `Val -> Type` value as of
   `docs/record-type-values.md` — with `RefinesNat2` defined as
   `RefinesOn(λ (e: Val) => NatEnv(e), …)` over a `NatEnv` record packing `a`,
   `b`, the tail and the shape proof. The family binders did not go away; they
   moved into a *domain predicate*, which is where they belong, and the two
   refinement theorems pay one transport along `NatEnv`'s shape proof for the
   move.

   The proof shape is the second finding, and it is the one that generalizes.
   The two IRs walk different environments, so there is no slot-by-slot
   transport of one invariant into the other, and none is needed: **each side
   is certified independently against the spec function, and functionality of
   `eval` glues them**. `eval_functional` (two convergent runs at different
   fuels agree — raise both to `n + m`, then `inj` on `Out`) turns the
   hypothesis's unknown `vs` into the value the first certificate names, and
   the second certificate discharges the conclusion. No simulation diagram, no
   bisimulation, no relation between the two executions at all. The
   env-independence the round expected shows up where the design predicts:
   `LetMatch` arms are *lexical* (note 5), so the recursive IR's arm sees the
   caller's environment underneath its own slots, and its invariant has to
   quantify over that tail — the recursive call builds a **closed** two-slot
   environment, so a tail-fixed statement could not be applied to its own
   induction hypothesis. `add_rec_env_indep` / `add_loop_env_indep` state the
   consequence equationally. Note that the general form of the claim ("the
   answer depends only on the slots the body reads") is **false** here for the
   same reason the unrestricted `Refines` is: junk fields shift the arm
   environment, and a shifted read reaches into the tail.

**Landed the same day** (was: deferred to the next round): §11 items 3–4.
Both blockers were called correctly. `fuel_monotone` *is* an IH-generalizing
induction, and the manual explicit-motive route works — one session, and the
whole case analysis lives in a single non-recursive lemma (`step_mono`) so
that the induction on fuel is two arms. Stating `converges` did want Σ, does
not have it, and took the computed-bound form; note 7 records what that
costs and why it costs nothing later.

9. **Fuel is internal, and the working object is the modality, not the
   number** (2026-08-02, agreed in discussion after the certifying
   generator's v2 round; the sharpened form of §6's "raw fuel appears in
   `simulate`'s definition and nowhere else"). No specific fuel value
   provides information at the statement level: what a statement is ever
   about is membership in "computes within finite time", and `Converges`
   *is* that possibility modality — the fuel is its hidden witness, and
   the algebra proofs work in is the closure's (implication chaining,
   `fuel_monotone` as the coherence lemma), not arithmetic over witnesses.
   The v2 round is the empirical half: everywhere a number appeared in a
   statement, composition broke — a caller's bound contains the callee's
   at an open argument, and no reducing spelling exists for the sum —
   and everywhere only the modality appeared, composition was the
   ∃-composition kit folding one lemma per instruction. So the discipline
   hardens from style to rule: *bounds in statements are compositional
   debt; the modality is the public form.*

   The flip side, recorded so this note is not read as "quantitative data
   is worthless": some consumers genuinely want the number — complexity
   certificates, cost-model refinements, a scheduler. That is an *opt-in
   quantitative layer* over the same runs (the bounded `refines` form that
   deliberately stayed in the library is its seed), not the default
   statement shape, and its ergonomics are a proof-automation problem: a
   bound is exactly the kind of witness a tactic synthesizes and a human
   should not spell (`issues/surface-proof-automation.md`,
   `issues/congruence-by-anti-unification.md`'s goal-solver shape). Until
   that machinery exists, the split stands: modality in statements,
   numbers in fixtures and in whatever quantitative theorems a consumer
   explicitly asks for.

10. **The landed extrinsic nodes do not carry output arities** (2026-08-19,
    found by the certified constant-match-fusion pass). Section 3's region
    model assigns every node an output arity, but the chain encoding in
    `lib/certgen/ir_v1.hthr` binds whatever `Val` spine its sub-region returns:
    `LetMatch`, `LetLoop`, and `LetCall` contain no arity field. Evaluation is
    total because malformed arities are merely data; reference rewriting is
    not. A pass cannot lift a slot map through one of these binders without
    knowing how many leading references belong to its outputs.

    The first constant-match fusion therefore takes the maximal arity-free
    case: a fresh `LetCon` immediately followed by `LetMatch(0, ...)`, with
    both the statically selected arm and the continuation equal to `Ret`.
    Their explicit `Refs` lists provide both prefix lengths structurally, so
    the pass can compose `fields ++ con ++ env` and
    `arm_outputs ++ con ++ env` exactly. General instruction-chain splicing
    waits for an arity source—an IR field, a checked side table, or the
    intrinsically scoped target from §8—and must not infer one from successful
    fixtures.
