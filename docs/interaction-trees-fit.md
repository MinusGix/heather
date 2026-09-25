# Interaction trees against Heather's type theory

Date: 2026-09-24. An investigation, not a design: where Xia et al.'s
*Interaction Trees* (POPL 2020, `docs/3371119.pdf`) would sit well in
Heather, where it would choke the kernel, and where it is odd without
being wrong. Owner of the eventual decision: `issues/effects-direction.md`.
The nearest live customer: `issues/linux-syscall-trace-model.md` ("an event
list over a relation, or an interaction tree").

## 0. Bottom line

- **Nothing in ITrees threatens consistency** as long as bisimilarity
  stays a *proposition* and never becomes part of conversion. Put strong
  bisimilarity into conversion and it is a semi-decision. Put weak
  bisimilarity (eutt) there and it is the halting problem. Both are easy to
  do by accident, through the kernel's own habit of giving η arms to
  negative types (§3.2).
- **The real walls come before the kernel.** Today's surface cannot write
  even a *finite* ITree. It rejects recursive function-typed fields
  (`reject_function_fields`). It has no `Type`-indexed families. And
  non-cumulativity with no lift makes the paper's
  `E : Type → Type` / `∀X. E X → M X` style a level problem everywhere
  (§2). All three walls go away if events are written as **containers**
  (`Cmd : Ty l`, `Resp : Cmd → Ty l`), which is what the Agda IO line does
  anyway.
- **Most of the value needs no coinduction.** Trees cut off at a given
  amount of fuel, plus the paper's own §7 result (eutt coincides with
  finite-trace equivalence), fit the `converges` / `fuel_monotone` interface
  `simulate` already exposes (`docs/ir-simulate-design.md` §6). Liveness is
  what that route loses.
- **If coinduction does come, Heather is better placed than Coq.** The
  kernel has no `fix`/`cofix`: recursion is eliminators, so corecursion
  would be a *corecursor*. A corecursor needs no guard checker, and a
  negative `M` avoids Giménez's subject-reduction break. The paper spends a
  lot of effort on both problems (§1, fn. 2–3). The long pole is the
  ch. 07 logical relation (§3.4), not the algorithm.

## 1. What the paper actually leans on

In the paper's own §9 terms, ITrees use three Coq features: coinductive
types, higher-order (large) types, and extraction. The full list is
longer:

| ITrees relies on | Heather today |
|---|---|
| `CoInductive itree` (negative, with `observe`) | no coinduction (DESIGN.md "Explicitly out of v0") |
| `Vis {A : Type} (e : E A) (k : A → itree E R)` — a constructor quantifying over `Type` | non-cumulative, no lift; `UPi` is layer m only |
| `E : Type → Type`, indexed by the answer type | indexed families take declared index types, not `Type<n>` heads |
| `k : A → itree` — a recursive function-typed field | `reject_function_fields` (tier-2 W lowering not generated) |
| Tau for guardedness, `iter`/`mrec` as the only knot-tiers | no guard checker needed (no `cofix`) |
| `eutt := nu euttF` via paco, relations into `Prop` | predicative only; impredicative Prop rejected |
| setoid rewriting with `Proper` instances | setoid roadmap (`issues/setoid-*.md`) |
| `MonadIter` for the predicate monad "via impredicativity of Prop" (§4.1) | unavailable, see §3.7 |
| extraction plus an OCaml driver with `Obj.magic` (fn. 8) | `runtime_fn` + datarepr, no extraction |

## 2. Surface walls, and the container fix

**Recursive function fields.** `Vis(e, k: A -> ITree)` is exactly what
`crates/elab/src/inductive.rs` `reject_function_fields` refuses. That makes
it a tier-2 (W-lowered) inductive, and the tier-2 generator is unbuilt
(`issues/inductive-compiler.md`, 2026-07-26 log: the same blocker sits in
front of surface `Acc`). This is the right lowering, not a workaround. The
branching-inductives decision chose `Wf` for *finite* children because
their η already lives in Σ/Unit. A `Vis` continuation, though, branches
over the *answer type*, which is `Nat`, bytes, and so on. It really is
infinitely branching, and `W` with Π-children is its honest home. So ITrees
in any form sit behind tier 2. They are a good driving example for it.

**Levels.** In the paper's form, `Vis` has a field `A : Type`, so
`itree E R : Ty (1 + l_E ⊔ l_R)` is one level up from its events.
Handlers `∀X. E X → M X` are one level up as well. `mrec` loops over a
state of type `itree (D +' E) R`, so it needs `itree` at two levels at once.
With no lift and no `UPi` below layer m (`issues/surface-universe.md` §3–4),
every one of these becomes generator-monomorphized copies with exact level
bookkeeping. It can be done, but it is friction that buys nothing.

**Type-indexed events.** `Get : stateE S S` would ford through
`sEq(Ty 0; R; S)`. That is an index at a *code* position, which is exactly
where `docs/sprop-design.md` records the head-only strip gap ("Same at
`Fin` and at `El` of a transported code"). A handler generic in `R` would
carry a stuck `transp` whose strip fires only once `R` is concrete. That
still works (trigger makes it concrete), but it is a place where
incompleteness and the event encoding meet.

**The fix is containers** (McBride's `General` from the paper's §8.3, and
Hancock–Setzer / Abel–Adelsten–Setzer in Agda):

```
record Events<l> { Cmd: Type<l>, Resp: Cmd -> Type<l> }
itree(E, R) := W (s : R + Unit + E.Cmd). Pos(s)
   Pos(inl r) = Empty,  Pos(tau) = Unit,  Pos(cmd c) = E.Resp(c)
handler      := (c : E.Cmd) -> M(E.Resp(c))        -- no ∀X, same level
E +' F       := { Cmd: E.Cmd + F.Cmd, Resp: case … }
E -< F       := container morphism (forward on Cmd, backward on Resp)
```

Everything stays at one level. No index fording, no `transp`. Handlers are
plain dependent functions. The subevent typeclass becomes a morphism of
containers, which a typeclass can search for. `Pos` is a large elimination
into codes, and the kernel already does that at `Ty l` motives.

## 3. Kernel: adding coinduction

If the kernel ever grows coinductive types, this is the shape that fits it
and where it would hurt.

### 3.1 The former

A negative `M^{l,l'}(x:S). T`: the dual of `W`, with destructors and a
corecursor, and no constructors or `cofix`:

```
out    : M → Σ(s : S). (T[s] → M)
unfold : Π(X : Ty k). (X → Σ(s:S). (T[s] → X)) → X → M
β      : out (unfold X c x) ⇝ (fst (c x), λy. unfold X c (snd (c x) y))
```

Why this and not Coq's shape:

- **No guard checker.** Productivity holds by construction, just as
  termination does for `elim_W`. The paper's complaint about
  non-compositional guardedness (§2, §4) disappears at the kernel. It
  reappears in the elaborator, which must compile guarded corecursive
  definitions into `unfold` the same way it compiles structural recursion
  into eliminators. `bind` needs a sum carrier (`itree E R + itree E S`).
  `iter` needs Tau.
- **No subject-reduction break.** Giménez's counterexample needs positive
  coinductive types, with `cofix` unfolding only under `match` (the paper's
  fn. 2).
- **No infinite δ.** Globals cannot be self-referential, so `echo :=
  unfold …` is an ordinary δ to a canonical form. The δ-lazy machinery and
  glued globals are untouched.

### 3.2 The choke point: η

The kernel's convention is that negative formers get a type-directed η arm
in `Conv::tm_nf`: Π, Σ and Unit do, and sEq gets an irrelevance arm. **`M`
must not get one.** η at `M` compares `out a ≈ out b`. That descends
through Σ-η into a Π-η at a fresh `y`, and lands on `M` again. On two
`unfold`s with different coalgebras that describe the same tree, it never
stops. It is a semi-decision for strong bisimilarity: it finds a difference
if one exists and runs forever otherwise. Fuel would turn that into
`OutOfFuel`, so the kernel stays total. But the *declarative* system would
then contain bisimilarity, and ch. 08's decidability would be gone. (Agda
leaves η off for coinductive records for this reason.)

So conversion at `M` stays intensional:

- `unfold X c x ≈ unfold X' c' x'` compares `X, c, x` componentwise.
- `unfold … ≈ neutral` is `NotConvertible`.
- Neutrals are compared by spine.

That is decidable, and ch. 06's WHNF/neutral grammar just gains `out` as a
neutral eliminator.

Weak bisimilarity (eutt) must stay out of conversion at any cost: deciding
`t ≈ spin` is halting.

### 3.3 Sharing in the β rule

The β above mentions `c x` twice. The environment machine shares it within
one step. Across the separate `fst` and `snd` observations it recomputes
it, which is the copattern cost and is acceptable. **The `reduce.rs`
rewriter is the problem.** It is the differential oracle, and it
substitutes syntactically. With n nested observations, the carrier term it
builds doubles at every layer. This is `issues/whnf-sharing-term-growth.md`
again, now inside the oracle, so the oracle would need a sharing-preserving
β for `M` (or a `let`) before the differential tests could cover deep
observation.

### 3.4 Metatheory (ch. 07) is the long pole

Reducibility at `W` is inductive. At `M` it is not, and the obvious
definition is circular. `unfold`'s carrier `X` may live at any level
(standard formulations leave `k` free), and even if `k` is pinned to
`M`'s level, `X` is not structurally smaller than `M`. So "reducible at
`M` = whnf is `unfold X c x` with `c, x` reducible" asks for `⟦X⟧` before
it exists. There are two ways out:

- an observational greatest fixed point ("`out m` is reducible at
  Σ(s:S). T s → M"), which puts a gfp inside the reducibility definition,
  or
- the ω-intersection `⟦M⟧ = ⋂ₙ Rₙ` with `R_{n+1}(m) := out m ∈
  ⟦Σ(s:S). T s → Rₙ⟧`. This needs only induction on `n`, which is friendlier
  to a predicative Coq development.

Either way it touches a shared notion (the reducibility universe). By
`coq-delam-formalization`'s own ranking, that makes it an
expensive-to-unwind edit to check first, not a per-former case.

### 3.5 Codes and the □ firewall: fine

Adding `M` means about four more code-recursor branches (`ty_m`, `tm_m`,
`tm_unfold`, `tm_out`; 52 → 56). At layer c nothing computes, so a boxed
corecursive definition is a finite piece of syntax. `□` comparison stays
syntactic, so bisimilar-but-different code stays distinguishable as code.
That is the same containment the design already gives funext.

### 3.6 The coinduction principle is an identification axiom

With β alone, `M` has no uniqueness of `unfold`, so "bisimilar ⇒ `Id`" is
not derivable. It has to be postulated, as funext would be. The
consequences are the usual ones, plus a Heather-specific sharpening:

- `J` along the axiom is stuck on closed terms, so canonicity is lost for
  anything that transports along it.
- The `sEq` strip fires only when the endpoints **convert**, and bisimilar
  `M` values do not. So a `transp` along an `sEq`-valued bisimulation axiom
  never strips, at any instantiation.
- The road where equality *computes* to bisimulation is OTT's (sEq reducing
  on type structure). `docs/sprop-design.md` §4 explicitly declined it
  ("Not OTT-style cast between types").

In the vision memo's terms (Code as *observation* primitive vs
quotients/funext as *identification* primitives), bisimilarity-is-equality
is squarely in the haunting column. Keep eutt a relation.

### 3.7 Predicativity

`nu euttF` (paco) is Knaster–Tarski: `∃ R. R ⊆ F R ∧ R t u`, which
quantifies over all relations. It stays in `Prop` only because `Prop` is
impredicative. Predicatively, `eutt` at level-l trees is a level-(l+1) type,
and with no lift that shows up everywhere. The paper's `MonadIter` instance
for the predicate monad (§4.1) is also out. There are two predicative
options:

1. an indexed `M` over pairs of trees (coinductive families: indexed `M` by
   fording), or
2. step-indexed: `eutt t u := Π n. euttₙ t u`, where each `euttₙ` is
   inductive (the Tau-peeling rules stay inductive, and `EqTau`/`EqVis`
   consume an index). It is small, it lives at the trees' level, and it
   needs no kernel change. **Conjecture, unproved:** for *deterministic*
   trees, which ITrees are, the ω-approximants meet at the gfp. Milner's
   classic gap between approximants and bisimilarity needs image-infinite
   nondeterminism. This needs a proof before anything rests on it, and
   choice trees (§6.2) would reopen it.

### 3.8 Quotienting by eutt costs countable choice

If the user's eventual quotient story reaches ITrees: Chapman–Uustalu–Veltri
show that the delay monad quotiented by weak bisimilarity is a monad only
with countable choice. Altenkirch–Danielsson–Kraus's partiality monad uses a
quotient inductive-inductive type (QIIT) to avoid that. ITrees inherit the
problem. This backs the paper's own choice, and the project's current one:
setoids.

## 4. The route that needs no kernel change

**Trees cut off at fuel `n`.** Take an inductive (W, tier 2) tree with a
`Cut` leaf, and let the semantics be a family `approx : Nat → tree` that
unrolls `iter`/`mrec` `n` times. Then:

- `terminates(t, r) := ∃n. approx n` reaches `Ret r` without cutting. This
  is `converges`, verbatim in shape.
- `traces(t) := { tr | ∃n. is_trace_of(approx n, tr) }`, with the paper's
  Fig. 20 `is_trace_of` unchanged, since it is already inductive. §7 proves
  eutt coincides with (finite) trace equivalence, so trace inclusion is the
  refinement notion and loses nothing that eutt would see for deterministic
  trees.
- Monotonicity in `n` is `fuel_monotone`, proved once.

What it buys: every structural law in the paper's Fig. 5 is *definitional*
in the inductive encoding, because `bind (Ret x) k ⇝ k x` is `elim_W` β.
That includes `x ← Ret v ;; k x ≅ k v`. Coq gets this only as a lemma,
because `cofix` computes only under `observe`. Safety and I/O-conformance
statements (every finite interaction the program has is allowed by the
spec) are all first-order over finite traces.

What it loses: liveness stated as a coinductive fact ("it responds
forever"). The part of liveness that is `Π`-over-finite-prefixes
(`∀ prefix ending in a request, ∃ extension with a response`) is still
expressible. Only a statement about a *completed* infinite behaviour is
out of reach.

This is also the substance of the "weaker finitary notion" that
`effects-direction` asks about: it exists, and it is the paper's own §7.

## 5. Oddities that are not problems

- **The discharge style changes.** Heather's certificates are
  conversion/evaluation (`refl` once a concrete IR makes `simulate`
  unfold). ITree equations are eutt, so proofs become rewriting chains,
  which is what the paper's §5 is. Generators would emit rewrite certificates
  rather than let the kernel evaluate. That needs setoid infrastructure and
  makes checking cost proportional to the proof, not the run.
- **The kernel evaluates continuations symbolically, until control
  branches on the answer.** `Vis e k ≈ Vis e k'` goes through Π-η, i.e. `k`
  and `k'` applied to a *fresh neutral answer*. Conversion therefore
  executes both continuations symbolically and succeeds when they branch
  identically on the input. Machine code branches on flags, not on source
  `if`s, so that is exactly where a proof has to take over. (The same
  substitution argument that justifies the probe classifier in
  `eval/probe.rs`.)
- **Left-nested binds are quadratic to observe.** `iter`'s loop body is
  `bind`'s left argument on every iteration, so reading depth `n` of a
  loop's tree by kernel evaluation (a `refl` over n bytes of `wc -l` input)
  re-traverses the bind stack. Codensity or type-aligned-sequence
  representations fix this, but they change the canonical forms and
  therefore what converts. Prefer not to observe deep trees by conversion.
- **Squashing eutt is mostly harmless.** eutt proofs are consumed almost
  only to produce other eutt or trace facts, which are squash-headed goals.
  The `truncated-witness-cannot-refute` trap bites only when an eutt proof
  must yield a relevant `Σ` (e.g. extracting the returned value), so keep
  eutt relevant, or reflect the pieces you extract.
- **Non-cumulativity and `Fin`.** The paper's `asm A B := fin A → block
  (fin B)` arithmetic is partly *definitional* here: `Fin(S k) ⇝ Unit +
  Fin(k)`, so `case_`/`inl_`/`inr_` at a concrete `Fin(a + b)` reduce. At a
  neutral `a` they are stuck, as expected.

## 6. Where it would be neat, beyond "effects"

### 6.1 The Linux trace model (the live customer)

`LinuxRuns` is an inductive relation, existential over runs. Its open
question is "Determinism … a theorem about `FetchedStep` or built into the
trace relation". An ITree answers it **structurally**. A machine's
denotation `run : State → itree LinuxCmd Status` is a *function* of the
responses, so there is exactly one tree, and `LinuxRuns` becomes its
`is_trace_of` set (§4). Error returns become answers
(`Resp(read) = Bytes + Errno`), and "the program handles EINTR" is a
statement about one subtree. The world is CompCert's coinductive `world`
from §8.4, but it needs no coinduction here. A history-indexed oracle,
`List (Σ c. Resp c) → Π c. Option (Resp c)`, is inductive-only and says
the same thing for finite traces. Given `issues/linux-syscall-trace-model.md`'s
"Shape" bullet, this is the strongest near-term argument for the container
ITree: the machine side and a future surface effects model can share one
event container.

### 6.2 Compositional CFG certificates

The paper's §5 case study is a certifying compiler over a traced monoidal
category: `app_asm`/`loop_asm`/`relabel_asm`/`pure_asm` with denotation
equations, and then `seq_asm`/`if_asm`/`while_asm` by rewriting alone. That
is the shape the native line reaches for:

- `docs/certified-pass-algebra-probe.md` is "one constructor-local law per
  clause, one generic induction". The paper's `compile_correct` is exactly
  that, with the relation being eutt after interpretation.
- The loop generators emit one certificate per loop. KTree `loop`'s
  equations (fixed point, parameter, composition, codiagonal) are what would
  let certificates for *linked* blocks compose by rewriting instead of being
  generated whole.

Choice trees (Chappe et al., POPL 2023) are the follow-up if concurrency is
what finally forces the issue, which is `effects-direction`'s stated
trigger.

### 6.3 Proper instances minted from code

The paper names the practical sore point of setoid rewriting: anonymous
functions defeat `Proper` search (§2.2). Heather can inspect code. A code
recursor over `□(Γ ⊢ f : A → itree E B)` can *derive* `Proper eutt f` when
`f` is built from proper combinators (bind, iter, interp, case_, …), as a
structural logical relation over syntax. This is the vision memo's
"disciplines as intensional analyses minting typeclass evidence", and it is
a concrete, bounded instance of `issues/setoid-auto-lifting.md`.

### 6.4 Effect signatures as contextual modal contexts

DeLaM already has `□(Δ ⊢ T)`. Read Δ as the effect signature
(`read : Unit → Bytes ⊢ t : T`): handling by `letbox` plus a substitution
`δ` that implements `read` is capability-passing semantics. This is
Zyuzin–Nanevski's ECMTT, whose `□` is contextual in exactly this sense. Two
limits to know up front:

- substitution gives only *tail-resumptive* handlers, with no access to the
  continuation, and
- the code recursor's variable branch (ch. 04, `t_x`) receives a layer-v
  variable it cannot compare, so a metaprogram cannot ask "is this the
  `read` op?" and build a `Vis`.

Continuation-capturing handling therefore goes through ElabCode (where a
call is named data) or through a source already in monadic form. This is
where Heather's modal half and ITrees would actually meet, and it is
unexplored.

### 6.5 The two effects leanings compose

`effects-direction` has uniqueness threading first and ITrees later. The
paper's §3 says these are layers of one semantics, not rivals:
`interp_state` of syscall events into a `World` state monad *is*
world-threading semantics. Threading is the interpreted view of the tree.
One denotation can serve both, and uniqueness typing then becomes the
static discipline that makes the interpreted view sound for a real world
that cannot be copied.

### 6.6 `mrec`: recursion as events

McBride's trick (recursive calls as `D` events, knot tied by `mrec`) gives
`runtime_fn` a fuel-free semantics for arbitrary recursion without
Bove–Capretta domain predicates, which `ir-simulate-design` notes want
function-typed inductive fields, the same tier-2 wall as §2.

## 7. Suggested order, if this is pursued

1. Tier-2 (W-lowered) surface inductives. Needed by every route, and by
   `Acc` too.
2. Container events plus the fuel-indexed tree, `is_trace_of` and trace
   refinement, as a library. Prove the §4 bridge to
   `converges`/`fuel_monotone`. No kernel change.
3. Re-express `LinuxRuns` as the trace set of a machine denotation, when
   the trace issue reaches determinism or `write`.
4. Only if liveness or concurrency demands it: a negative `M` with β only
   (§3.1–3.2). Check the reducibility edit (§3.4) in the Coq formalization
   *before* the kernel round, as a shared-notion edit.

## Sources

- Xia et al., *Interaction Trees*, POPL 2020 — `docs/3371119.pdf`.
- Frumin, Timany, Birkedal, *Modular Denotational Semantics for Effects
  with Guarded Interaction Trees*, POPL 2024 — `docs/2307.08514.pdf`; the
  guarded-recursion route, and higher-order effects plain ITrees cannot
  express.
- Chappe et al., *Choice Trees*, POPL 2023 — nondeterminism/concurrency.
- Chapman, Uustalu, Veltri, *Quotienting the Delay Monad by Weak
  Bisimilarity*, ICTAC 2015 / MSCS — countable choice;
  `docs/chapman-uustalu-veltri-delay-quotient.pdf`.
- Altenkirch, Danielsson, Kraus, *Partiality, Revisited*, FoSSaCS 2017.
- Zyuzin, Nanevski, *Contextual Modal Types for Algebraic Effects and
  Handlers*, ICFP 2021 — `docs/2103.02976.pdf`.
- Ahrens, Capriotti, Spadotti, *Non-wellfounded Trees in HoTT*, TLCA 2015;
  Avigad, Carneiro, Hudon, *Data Types as Quotients of Polynomial
  Functors*, ITP 2019 — M-types built from approximations with no kernel
  support (Lean's route), where `dest (corec f x)` is a theorem, not a
  reduction.
- Abel, Adelsten, Setzer, *Interactive Programming in Agda — Objects and
  Graphical User Interfaces*, JFP 2017 — container-style IO trees.
- Fadaei Ayyam, Sammler, *HITrees: Higher-Order Interaction Trees*
  (2025) — `docs/2510.14558.pdf`; higher-order effects (parallel
  composition, call/cc) that plain ITree events cannot express. Not yet read
  in full.
