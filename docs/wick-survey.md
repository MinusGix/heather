# Wick survey: what Heather's machine-learning area should take

Status: **survey**, 2026-10-21. Owner issue: `issues/wick-survey.md` (the
`ml-survey` milestone in `docs/roadmap.md`). Follow-up issues are listed in
§8.

Wick (`MinusGix/wick`, private) is Minus's Lean 4 project formalizing machine
learning: an architecture library, optimisation theory, and a large research
tower on deep-learning theory. This note says what it contains, which of it is
worth having in Heather, what should be done fundamentally better rather than
transcribed, and what mathematics and programming tooling Heather needs before
any of it can land. As with Flean for floats (`docs/floating-point-design.md`),
the goal is to learn from Wick, not to port it.

Everything here was read from the source at `b1b88a2` (2026-09-15, the last
commit), together with Wick's own design documents (`ARCHITECTURE.md`,
`ROADMAP.md`, `RESEARCH_THREADS.md`, `.claude/notes/research-vision.md`, the
per-directory `DESIGN.md` files and `docs/`). Wick was not built for this
survey; claims about proofs come from its sources and its own status notes.

---

## 0. The answer in brief

1. **Wick is big and mostly research.** 581 Lean files, about 158k lines,
   about 4.7k theorems, on Lean 4.27 with Mathlib. It is sorry-free except
   for a deliberately unverified `Float` wrapper. Roughly half the lines are
   the PDLT tower (*Principles of Deep Learning Theory*); the architecture
   library and gradient correctness are about a fifth; the rest is
   optimisation, symmetry, scaling laws, numerics and toy models.
2. **What transfers is the *design knowledge*, more than the theorems.** Wick
   ran into, and in its late documents correctly diagnosed, most of the
   problems a second attempt would hit: canonical structure found by
   typeclass search, hypothesis blowup, ordered-tuple moments, integrals as
   the primary definition, floats treated as a scalar. Heather should start
   from Wick's *revised* positions, not its original ones (§3).
3. **The one thing to do fundamentally better is to make models programs.**
   In Wick a model is a Lean function over an abstract scalar, it never runs
   except through a `sorry`-instanced `Float`, and the planned float track
   was never built. In Heather the same model source should evaluate exactly
   at `Rat`, be specified at `CReal`, run at `Float(F)` with an error theorem
   against the specification, and compile natively. That is where Heather's
   native compiler, interaction trees and float library pay off together
   (§3.1).
4. **The second is constructive, algebra-first mathematics.** Wick leans on
   classical Mathlib analysis, measure and probability (224 files touch
   `MeasureTheory`). Its own late refoundation moved moments to *states on an
   algebra* and sums ahead of integrals, which is exactly the shape a
   constructive Heather wants: the combinatorial core of PDLT (Wick's
   theorem, cumulants, the linked-cluster theorem) needs no measure at all
   (§3.4).
5. **Heather is far from ready for most of Wick.** It has no finite linear
   algebra, no big operators over finite types, no derivatives, no
   combinatorics of partitions, no probability. §4 maps each need to an
   existing milestone or a new issue. The first ML milestone that is
   reachable soon is a small layer library with reverse mode proved once and
   a forward pass that runs at `Rat` and at `Float` (§6).

---

## 1. What Wick is

Wick is one of three repositories in one programme (from Wick's
`research-vision.md`): **Flean** (floats as a reductionist substrate; Heather's
float library already learned from it), **Wick** (a formalized "physics of
machine learning", inspired by PDLT), and **Wisp** (networks under floating
point, where the other two meet; it depends on both and is not surveyed here).
The animating bet is that floating point is a finite, sometimes simpler
substrate that can both reduce computation and clarify theory.

Wick itself has three layers, which matter differently to Heather:

| layer | directories | lines (approx.) | character |
|---|---|---|---|
| Architecture library | `Basic`, `NTensor`, `Linear`, `Attention`, `Transformer`, `Models`, `Normalization`, `Position`, `Softmax`, `Activations`, `Conv`, `Embedding`, `Gradient*`, `GradientCorrectness`, `Tied`, `Causality`, `Streaming`, `Optimizer`, `Training`, `Sampling`, `Generation`, `Typeclass`, `Derive` | 30k | engineering: layers, combinators, backward passes and their correctness |
| Optimisation theory | `Convergence`, `Optimizer`, `LearningRate`, `Dynamics` | 11k | classical theorems: convex, strongly convex and PL descent, SGD with filtrations, mirror descent |
| Theory research | `PDLT`, `Symmetry`, `Scaling`, `Numerics`, `Toys`, `Counting`, `GramLibrary` | 110k | research: PDLT chapters 1–5 and 7–11, Noether charges, scaling laws, asymptotics, toy models |

The repository also has 159 issues (116 open), each tied to one of about 25
research threads (`RESEARCH_THREADS.md`, T1–T24 plus infrastructure threads
T7–T11 and T19), and a large body of design and research prose. Its
`README.md` and `Wick/PDLT/README.md` are stale (the latter still says the
directory is only Chapter 1); `RESEARCH_THREADS.md` and `PDLT_ROADMAP.md` are
the current maps.

---

## 2. Module by module

The verdict column says what Heather should do with each part: **take** (the
results are wanted, restated in Heather's idiom), **redesign** (the subject is
wanted but Wick's design is not the one to copy), **later** (wanted once its
prerequisites exist), or **leave** (research in progress, or tied to Lean or
Mathlib specifics).

### 2.1 Architecture library

| part | what it has | verdict |
|---|---|---|
| `Basic`: `IdxSpace`, `NTensor`, `WithDim`, `VecIdx`, `Layer`, combinators | Tensors are functions `Index i → T` over an index-space class with named dimensions (`Batch`, `Seq`, …); `Layer L Idx I O` with `forward`; `Compose` (`⋙` on types, `>>` on values), `Fork`, `Parallel`, `AddPair`, `Residual`, `Stack`, `Repeat` | **redesign** (§3.2, §3.6). The combinator grammar is the right idea; the index-space hierarchy and the class-per-layer encoding are what cost Wick most. |
| `Parameters`, `Gradient`: `HasParameters`, `HasBackward` | Parameters as an `outParam` type per layer; a practical backward pass `(dx, dp)` that works for every layer (subgradients allowed), separate from smoothness claims | **take** the separation (practical backward vs. theoretical smoothness is right); **redesign** the encoding. |
| `GradientCorrectness` (10k lines) | Three levels: `BackwardCorrect` (a pairing identity `⟪backward dy, δ⟫ = ⟪dy, df δ⟫`), a linear-map level, and a Fréchet level; adjoint proofs for linear, biaffine, softmax, masked softmax, attention, causal attention and sublayers; `IsBackwardAdjoint` bridging to `fderiv` through `FlatCarrier` | **redesign** (§3.5). Wick's own roadmap notes the pairing level never anchors `df` to a real derivative (Phase 2, "connect df to fderiv", mostly not done). |
| `Typeclass`: `Exp`, `Tanh`, `Sqrt`, `Log`, trig, and law classes such as `TanhWeakBounded`, `ExpBotZero` | Small classes for operations and their laws, so theorems stay generic over the scalar and float-compatible forms are preferred (`-1 ≤ tanh ≤ 1`, `exp(-∞) = 0`) | **take** the habit of float-compatible law statements; but the float link should be refinement, not instantiation (§3.1). |
| `Typeclass/Pairing`, `FlatCarrier`, `Derive` | A tower of about 24 pairing instances; `FlatCarrier` (a canonical coordinate chart per carrier) and `deriving HasPairing, FlatCarrier` handlers | **redesign** (§3.2). This is the clearest case of "a function of type structure implemented as a search". |
| `Attention`, `Transformer`, `Models` | Attention kernels, multi-head, GQA, RoPE, KV sharing; blocks, FFN, GPT, Llama, Mistral; KV cache with batch/streaming equivalence; prefix causality (`IsPrefixCausal`) | **later**. The KV-cache and causality theorems are program-equivalence results and fit Heather well; the model zoo should wait until the core is good. |
| `Softmax`, `Attention/Dispersion`, `ScorerResolution`, `Counting` | Softmax dispersion lemma (Veličković et al.) proved both-sided and tight, the `log n` sharpness budget, the scorer `1/η` law, Hahn's single-edit bound giving a Dyck-1 ceiling for normalized heads | **take** later as showcase results: they are short, elementary, and say something real about architectures. |
| `Conv`, `Position`, `Normalization`, `Activations` | 1D/2D convolution with padding variants, sinusoidal and rotary positions, LayerNorm/RMSNorm, GLU, activation bounds | **later**, as layer-library breadth. |
| `Tied` | Weight tying through adjoint contracts; oracle transfer for tied parameters | **later**; the adjoint-contract formulation is good and should be kept when it comes. |
| `Training`, `Sampling`, `Generation`, `Examples` | Training loop, sampling, decoding; `TrainLinear` runs regression on `FloatR` | **redesign**: these are where "models are programs" (§3.1) starts. |

### 2.2 Optimisation theory

| part | what it has | verdict |
|---|---|---|
| `Convergence/Convex`, `PL`, `GradientDescent` | L-smoothness, strong and first-order convexity, cocoercivity, descent lemma; PL linear convergence for GD and for gradient flow (Grönwall) | **take**. Deterministic and finite-dimensional; the first theorems an ML library should own. Stated over an ordered field where possible. |
| `Convergence/SGDProcess`, `Filtration`, `StochasticOracle`, `MirrorProcess`, `Pairing*` | SGD convergence for smooth and strongly convex losses via conditional expectation on filtrations; mirror descent; a dual-space pairing-oracle theory | **later**. Heavily measure-theoretic. Over a finite dataset with uniform sampling, the same results have finite-expectation proofs that Heather can state much earlier (§4.4). |
| `Optimizer/Adam`, `Momentum`, `LearningRate` | Definitions; Adam convergence is an open issue | **take** the definitions when the layer library lands; no theorems to port. |

### 2.3 Theory research

| part | what it has | verdict |
|---|---|---|
| `PDLT` chapter 1, `Numerics/Combinatorics` | Isserlis/Wick theorem via perfect matchings, Gaussian moments, cumulants (recently refounded as states on an algebra with Rota/Möbius inversion on the partition lattice), perturbation theory, the sharp linked-cluster theorem (connected 2m-point correlator is `O(ε^{m-1})`) | **take**, algebra-first (§3.4). This is the most reusable mathematics in Wick, and its combinatorial core is measure-free. |
| `PDLT/Kernel`, `NTK`, `DeepLinear`, `Networks`, `Perturbation`, `LinkedCluster*` (≈ 60k lines) | Kernel recursion, criticality, depth laws; NTK and dNTK statistics; lazy-training convergence with high probability for a two-layer tanh network; deep linear networks; the ε ↔ 1/n width bridge | **leave** for now. It is the deepest part of Wick and the most dependent on classical Gaussian integrals over ℝ. Revisit once Heather has Gaussian states (§4.4) and real functions (§4.3). |
| `PDLT/Hermite`, `Sphere` | Hermite polynomials, Mehler, Gaussian–Sobolev order and truncation rates, completeness of Hermite functions in `L²(γ)`, ReLU's Hermite order | **later**. The polynomial and coefficient-level parts are algebra and could come early; completeness is analysis. |
| `Symmetry` (9k) | Noether identity for gradient flow, conserved charges and their breaking by discretisation and weight decay, completeness of conservation laws (Marcotte–Gribonval–Peyré: bracket saturation is a matrix commutator computation) | **later**. Mostly finite-dimensional linear algebra and calculus; a good second customer for linear algebra. |
| `Scaling` | Resolution-limited `D^{-1/d}` scaling, a unified exponent `D^{-sρ/(d-k)}`, effective dimension `tr(K(K+κI)⁻¹)`, intrinsic (box-counting) dimension | **later**. |
| `Numerics/Asymptotics`, `Acceleration`, `Iteration` | Gevrey series, Borel and Borel-2 summation, Stieltjes moments; Richardson and Shanks acceleration; Newton, Newton–Schulz, Banach fixed point | **later**, with the asymptotics area of mathematics (roadmap item 5). Newton–Schulz and Richardson are also numerics a float library could prove at `Float`. |
| `Toys` (identity, deep linear, low rank, parity, modular addition), `GramLibrary` | Concrete networks where the abstract theorems become hypothesis-free: identity-network NTK spectrum, balancedness as a Noether charge, Fourier solution of modular addition | **take** the method (§3.8). In Heather many of these known-answer facts are decidable by evaluation at `Rat`. |

---

## 3. What to do fundamentally better

Minus's judgement in the owner issue is that Wick needs real work, not
transcription. Wick's own late documents agree in most places and say where.
Each point below names the Wick evidence and the Heather design it suggests.

### 3.1 Models are programs

**Wick.** The stated philosophy is "a flexible scalar type: reals (proofs),
rationals, or floats (computation)" and "we're formalizing, not executing".
In practice nothing executes: `Typeclass/FloatR.lean` wraps Lean's `Float`
with `sorry` for every algebraic law, `Examples/TrainLinear` is the only
runner, and the experiments behind the research threads are Python scripts
(`scratchpad/*.py`, `docs/*/sims/`). Wick's architecture review then
concluded that **floats are not a scalar** (`ARCHITECTURE.md` §2.1, §2.6): the
real layer is the specification, a float layer is an implementation chosen by
an algorithm (for example the summation order of a matmul), and the link is a
refinement theorem `‖floatForward x − realForward x‖ ≤ ε` that composes
through the combinators the way Lipschitz constants do. That float track
(phase B4) was never built.

**Heather.** Start from the revised position, and go further, because Heather
can run what it proves:

- One model source, generic over a scalar class, has three instantiations:
  `Rat` (exact; runs, and decides concrete facts by evaluation), `CReal` (the
  specification; constructive, so it also computes, slowly), and `Float(F)`
  (the implementation, with rounding chosen per operation).
- The float-to-real link is an error theorem per layer that composes along
  the combinator grammar (an error-propagation analogue of a Lipschitz
  bound). Its inputs are the float library's standard model and
  γ-composition (`float-error`) and the arithmetic theorems (`float-arith`).
- Training and inference loops are effectful programs; with interaction
  trees (`it-library`) and the native compiler, "this binary trains this
  network, and its float run stays within ε of the real-number training
  run" becomes a statable theorem rather than a slogan. That is the shape
  the GPU area wants later, too.
- Wick's Python simulations become Heather programs: the experiment and the
  theorem it checks share one source.

### 3.2 Compute canonical structure; search only for facts

**Wick.** `ARCHITECTURE.md` §0–§1 is the sharpest diagnosis in the
repository: "much of what typeclass resolution is doing here is a *function
of type structure* (the canonical pairing, the flattening, the param-type),
but it is implemented as a *search*". Symptoms: 89 `synthInstance` and
`checkSynthOrder` escape hatches; heartbeat overrides up to 16M; a pairing
whose concrete normal form depends on instance priorities, so `rfl` fails at
dozens of sites; diamonds from `extends` re-discovered repeatedly. The fix
(`FlatCarrier`, one coordinate chart per carrier) partly landed, and then the
collapse of the pairing tower onto it was found to be blocked (phase B3.2):
with the scalar an `outParam`, `Fin n → ℝ` is itself a semiring, so the chart
instance makes the scalar ambiguous and synthesis times out. The tower stayed.

**Heather.** Make the forced half a function from the start:

- Shapes are data. A tensor shape is a value of an inductive (dimensions with
  names and sizes), the index type is computed from it, and a tensor is a
  function on that index type. Pairing, flattening, the parameter type of a
  layer, and `+`/`0` on parameters are ordinary functions on the shape, with
  one definitional answer each.
- Open-world facts (Lipschitz, differentiable, backward-correct,
  well-conditioned) stay classes or explicit predicates, which is what
  Heather's relation-indexed classes are for.
- The scalar is a parameter, never inferred from the carrier. Heather has no
  `outParam`-driven inference to fall into, and should not add one for this.
- Where Wick needed `deriving` handlers (pairing, flat carrier, parameter
  records), Heather's generated code and derive machinery should produce the
  same artefacts from the shape, with the laws proved by evaluation or once
  generically.

### 3.3 Statements without hypothesis blowup

**Wick.** `research-vision.md` names this as the real blocker: "a dozen
baseline parameters on everything — and the blowup compounds". A
representative headline,
`secondLayer_lazy_gd_converges_whp_tanh_general`
(`PDLT/NTK/SecondLayerMeanPosTanhConverges.lean`), takes about thirty
hypotheses, among them `hCBdef : CB = 1 ^ 2 + 4 * 1 ^ 2 * X2` and five more
defining equations for constants, six width thresholds such as
`524288 * CH * CB * CL * (4 * EL0 + 1) * (nOut * N) ^ 3 ≤ n₁ * a_lo ^ 4`, and
problem data threaded by hand.

**Heather.** Treat this as a library convention, using features Heather
already has:

- Constants are definitions, not hypotheses with defining equations. Where a
  theorem needs a named constant, it is a function member of the theorem's
  owner (`theorem f::name`, the function-scoped names from the positivity
  rounds), so callers never restate it.
- Problem data is a record (inputs, targets, hyperparameters), and the
  regime is one named predicate on it (`WellConditioned`, `WideEnough`),
  proved separately. Wick's toys already discovered this
  (`WellConditioned μ L` on a `LinearTask`); make it the default shape.
- Side conditions the elaborator can discharge are parameter defaults
  (`h: 0 < n := positivity`, `:= omega`), and positivity is binder sugar
  (`n: Pos<Nat>`), not a hypothesis per constant.

### 3.4 Algebra first, measure at the boundary

**Wick.** The original philosophy made integrals the canonical definition and
finite sums a theorem (`CLAUDE.md`, "measure-theoretic foundations"), so every
finite path paid for the measure hierarchy. The architecture review reversed
this to **sum-first, integral as an opt-in** (§2.4, resolved fork 3), because
"every integral specializes straight back to a sum". Separately, the
algebraic refoundation (`docs/algebraic/REFOUNDATIONS.md`, thread T20)
replaced moment families indexed by ordered tuples with **states**
`φ : A →ₗ R` on a commutative algebra of observables; that deleted a whole
layer of `Fin.cast` plumbing at its root, and put cumulants on Möbius
inversion over the partition lattice. Its stated payoff: the same
construction over non-crossing partitions gives free cumulants.

**Heather.** This is the order a constructive library wants anyway:

- Finite sums over finite types are primary. Integration comes only where a
  genuinely continuous quantity is integrated, and arrives with the measure
  and probability work (roadmap mathematics item 4), possibly through
  valuations on locales.
- A Gaussian is first a state on a polynomial algebra, defined by Wick's
  theorem (the 2k-th moment is a sum over perfect matchings of products of
  covariances). Isserlis, cumulants, perturbation theory and the
  linked-cluster theorem are then algebra and combinatorics, constructive
  as they stand.
- The bridge "this state is integration against the Gaussian measure"
  becomes one theorem added later, not a foundation every result pays for.
- Expectations over a finite dataset or a finite sampling distribution are
  finite weighted sums; SGD over a finite dataset needs nothing more
  (§4.4).

### 3.5 Reverse mode defined once, anchored to a derivative

**Wick.** Every layer carries a hand-written `backward`, a hand-written
directional derivative `df`, and a proof of the pairing identity between
them. Composition is generic, but the identity cross-checks `backward`
against `df` without anchoring `df` to anything: a wrong `df` passes
(`ROADMAP.md` Phase 2). The Fréchet level exists for a handful of layers.

**Heather.**

- Reverse mode is a transformation over the layer grammar (and later over
  programs), defined once and proved once. Per-layer work is only the
  primitive rules (linear, pointwise, softmax, normalisation).
- Correctness is stated against a derivative Heather actually has. For
  polynomial and rational layers that can be the algebraic (formal)
  derivative, which needs no analysis; for `exp`, `tanh` and friends it is a
  constructive derivative on `CReal` (§4.3). The pairing identity remains
  the interface, now with `df` pinned.
- In the longer run reverse mode is a compiler pass, so it belongs with
  `hih-passes`: a Heather metaprogram with its proof.

### 3.6 Named dimensions without the index-space hierarchy

**Wick.** `IdxSpace` → `FiniteIdxSpace` / `MeasuredIdxSpace`, `HasDim`,
`UpdateDim`, `IterDim`, `SizedDim`, `SplitDim`, `WithDim` wrappers, and a
per-constructor `Fintype`/`DecidableEq` tax through the `Index` projection
(`ARCHITECTURE.md` §4, §6.0). `ARCHITECTURE_ISSUES.md` records the result:
`SplitDim` underused, dimension tags verbose
(`LinearDim DModel DFF R dModel dFF`).

**Heather.** Shapes as data (§3.2) cover this: a named dimension is a field
of the shape value, finiteness and decidable equality of the index type are
computed, and value parameters on inductives (`D<p̄>(v̄)`) carry sizes
without type-level tags. Wick's convention "curried over product indices"
(`Q : Fin seqLen → R[keyDim]`) is worth keeping as the default view.

### 3.7 Tactics and proof economy

Wick's `docs/TACTIC_OPPORTUNITIES.md` lists the shapes it wrote by hand:
unfolding backward-correctness preambles, reordering and splitting finite
sums, exhausting small `Fin n`, `funext` boilerplate, lifting derivatives
through Π, building linear maps, pushing ring normalisation through sums, and
a prospective exponent calculus for μP. Under Heather's "tactics everywhere"
principle these are customers of `tac-general` (rewriting and congruence)
and `tac-arith` (ring normalisation through sums). Its proof-simplification
register (`docs/PROOF_SIMPLIFICATION.md`) adds two lessons worth adopting:
admit an abstraction only when a **named theorem** is being proved repeatedly
in fragments (shared syntactic shape is not enough), and check the import
order first, because every long-proof cluster it examined hid a general lemma
sitting downstream of its own special case.

### 3.8 Known-answer anchors, by evaluation

Wick's toys are its best methodological idea: each abstract result is
instantiated on a concrete network with a known answer, which both makes it
hypothesis-free and exposes where the theory frays (the identity network's
NTK condition number grows linearly in width, entirely from the bias mode).
In Heather, many such anchors at concrete sizes are closed computations over
`Rat`: a Gram matrix, its positive-definiteness certificate (an `LDLᵀ`
factorisation checked by evaluation), a conserved charge along a few exact
steps. They should be proved by evaluation, the way the library already proves
closed facts, and the general-size theorem stated beside them.

---

## 4. What Heather needs

### 4.1 Mathematics

| need | why ML needs it | owner |
|---|---|---|
| The class hierarchy up to ordered fields | every scalar-generic statement | `math-classes` (in progress: semiring and ring layers; ordered field over commutative ring) |
| Big operators over finite types: `∑`/`∏` over `Fin n`, products and sums of finite types, reindexing, Fubini for finite sums | dot products, matmul, losses, expectations, pairings | design owned by `big-operator-semantics`; ML is a customer that fixes the finite case first |
| Finite linear algebra: vectors `Fin n → R`, matrices, transpose, matmul, quadratic forms, Gram matrices, positive (semi)definiteness with checkable certificates | layers, NTK Gram matrices, conditioning, symmetry results | **new** `finite-linear-algebra` |
| Real functions and derivatives: continuity with modulus, Lipschitz, a constructive derivative on `CReal`, `exp`/`log`/`tanh`/`sqrt` as real functions with their laws | smoothness, descent lemmas, activations, reverse-mode correctness | **new** `real-functions-and-derivatives` (serves `math-reals`; `float-transcendental` supplies correctly rounded `exp`/`log`) |
| Partition combinatorics: perfect matchings, set partitions as a lattice, its Möbius function | Wick's theorem, cumulants, the linked-cluster theorem | **new** `set-partition-combinatorics` |
| Finite probability: distributions with finite support and rational weights, expectation as a state, independence, variance | SGD over a finite dataset, sampling, stochastic rounding, finite-sample statements | **new** `finite-probability` |
| Measure, integration, Gaussian measure | continuous expectations (PDLT kernels, NNGP), the state-to-measure bridge | roadmap mathematics item 4 (measure and probability, possibly via locales); no issue yet, and none needed before §4.4's finite layer exists |
| Asymptotics: `O`/`o` on sequences, formal power series | width and depth expansions, scaling laws | roadmap mathematics item 5; later |

### 4.2 Floating point

The float library (`lib/std/float/`) already has formats as data (IEEE
interchange, bfloat16 and the OCP microscaling element formats), dyadic
values and rounding. ML pulls three further pieces, all already milestones:
`float-error` (the standard model and γ-composition, which is exactly what a
dot-product or summation error bound needs), `float-arith` (add, mul, fma,
div, sqrt), and later `float-transcendental` (`exp`, `log`) and stochastic
rounding, which waits on probability (`docs/floating-point-design.md` §5).
Low-precision formats (E4M3, E5M2, FP4) matter for ML specifically:
error bounds should be stated per format, not only for binary64.

### 4.3 Programming tooling

| need | owner |
|---|---|
| Tensors as data that the native backend can hold: shape-indexed arrays with computed index types, views for the curried and flat orders, executed without lists | **new** `ml-tensor-shapes` (the design); the heap needs `hih-memory` |
| A scalar-generic model can be instantiated at `Rat`, `CReal` and `Float(F)`, with a refinement theorem between the float and real runs | **new** `ml-scalar-refinement` |
| Layer grammar and reverse mode defined once | **new** `ml-layers-reverse-mode` |
| Training loops as effectful programs with stated traces | `it-library` (done) and `hih-program-logic`; nothing ML-specific yet |

---

## 5. What not to take

- **The `FloatR` stub** and any unverified scalar instance. If a scalar runs,
  its laws are proved or its link to the reals is an error theorem.
- **The pairing tower and the measured index hierarchy.** §3.2 and §3.6
  replace them.
- **SGD with filtrations and conditional expectation** as a first target.
  The finite-dataset versions say the same thing for the programs people run,
  with far less machinery.
- **Research threads still in motion.** T13 (odd symmetries) is parked; T16
  (learning dynamics) is discussion-stage; T17/T18/T21–T23 are scoped menus.
  They are Wick's research, not library material.
- **The model zoo before the core.** GPT, Llama and Mistral come after the
  layer grammar, reverse mode and the float link work on a small network.

---

## 6. ML milestones

Proposed here and adopted into `docs/roadmap.md` by Minus on 2026-10-22.

| milestone | done when |
|---|---|
| `ml-layers` | A layer grammar (linear, pointwise activation, compose, fork, residual) over computed shapes, with reverse mode defined once and proved against the formal derivative on polynomial layers, and a two-layer network that evaluates at `Rat`. |
| `ml-float-forward` | One small network's forward pass runs at `Float(F)` and at `Rat`/`CReal`, with a composed error theorem between them, using `float-error`. |
| `ml-descent` | Deterministic gradient descent converges on an L-smooth, strongly convex (or PL) objective over an ordered field, with one concrete known-answer instance proved by evaluation. |
| `ml-gaussian-states` | Gaussian states on a polynomial algebra, Wick's theorem by perfect matchings, and cumulants by Möbius inversion on the partition lattice. |

The recommended first round is `ml-layers`, after the finite big operators
and the start of finite linear algebra: it exercises shapes-as-data, the
class hierarchy and reverse mode at once, and it is the substrate the other
three state themselves over. `ml-gaussian-states` is independent of it and can
run in the mathematics lane as soon as partition combinatorics exists.

---

## 7. Open questions for Minus

1. **Scope of "bring Wick in".** Is the target the architecture library and
   optimisation theory (where Heather's execution story adds the most), or
   also the PDLT research tower? This note assumes the former first, PDLT's
   algebraic core second, and the rest of the tower only when Heather's
   analysis can carry it.
2. **Wisp.** Wisp proves forward, backward and SGD-step float drift for
   linear and MLP chains. It is the closest prior art for `ml-float-forward`
   and is worth a short look before that round; it is not attached to this
   project.
3. **Constructive derivatives.** The choice between a Bishop-style uniform
   derivative on `CReal`, a derivative on an abstract ordered field, and
   formal derivatives only (for polynomial layers) decides how much analysis
   `ml-layers` waits for. This note recommends formal derivatives first and
   `CReal` derivatives as their own issue.

---

## 8. Follow-up issues

Filed with this note:

| issue | area | what it owns |
|---|---|---|
| `ml-tensor-shapes` | machine-learning | Shapes as data, computed index types, canonical pairing and flattening as functions, the executable representation. |
| `ml-layers-reverse-mode` | machine-learning | The layer grammar and reverse mode defined once, proved against a derivative. |
| `ml-scalar-refinement` | machine-learning | One model at `Rat`, `CReal` and `Float(F)`, and the composed float-to-real error theorem. |
| `ml-gaussian-states` | machine-learning | Gaussian states, Wick's theorem, cumulants as Möbius inversion. |
| `ml-deterministic-descent` | machine-learning | GD convergence under smoothness and strong convexity or PL, with a known-answer instance. |
| `finite-linear-algebra` | mathematics | Vectors, matrices, quadratic forms, Gram matrices, PSD certificates. |
| `real-functions-and-derivatives` | mathematics | Continuity, Lipschitz, a constructive derivative on `CReal`, the elementary functions. |
| `set-partition-combinatorics` | mathematics | Perfect matchings, the partition lattice, its Möbius function. |
| `finite-probability` | mathematics | Finitely supported distributions, expectation as a state, independence. |
