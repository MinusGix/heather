# Programming in continuous time — survey

Survey of 2026-11-10. It reads Imada and Hsu, "A Hoare Logic for
Continuous-Time Stochastic Processes" (arXiv 2611.12761), and asks what the
area offers Heather when the aim is to *program* in continuous time and not
only to model it: write a program whose time is continuous, run it, and use
its continuous meaning to get better discrete answers. Probes:
`lib/_tests/std/analysis/continuous_time_tests.hthr`.

The paper's related work is cited from the paper; everything in §2 beyond it
is from memory and unchecked against the sources (arxiv is unreachable from
the cloud box).

## 1. The paper

**The language.** `pWhile_dt` is an ordinary probabilistic while-language
with one special variable `dt`. A continuous variable may only be updated by
`x += f·dt` (`f` Lipschitz) or `x += f·db`, where `db` is `+√dt` or `-√dt`
with equal chance. There are no differential equations and no continuous
sampling in the syntax. Brownian motion is

    t, x := 0; while (t < T) { t += dt; x += db }

**Two meanings.** The *discrete* meaning fixes `dt = ε > 0` and is Kozen's
measure-transformer semantics: a finitely supported distribution when the
loop surely terminates. The *continuous* meaning is the set of limit points
of the discrete outputs as `ε → 0` (the Kuratowski upper limit in each
Wasserstein metric, intersected over the orders, with the discrete-class
variables projected away). It is a *set* because the authors could not
guarantee one limit without restricting the language. Theorem 11: the set is
nonempty when the loop terminates surely and in bounded time (`ε·N(ε)`
bounded), proved with nonstandard analysis.

**The logic.** Assertions are about the output measure: expectations of
polynomially growing test functions and probabilities of events. There are
two judgements, `⊢d` (for every `dt`) and `⊢c` (for every limit). The rule
that carries the method is

    ⊢d {Φ} p {W}
    ------------  Transfer     (W a "Wasserstein-closed" assertion)
    ⊢c {Φ} p {W}

so a loop-invariant proof about the ordinary program, uniform in `dt`, is a
proof about the continuous process. `Conseq_c` then substitutes `dt := 0` in
the postcondition. A second loop rule handles invariants that hold only up
to `dt·e` per step. Ten processes are treated (Brownian motion in one to
three dimensions, escaping, reflected, absorbed, geometric, oscillating,
Ornstein–Uhlenbeck, a stochastic hybrid system), 21 properties, among them
all moments of Brownian motion, which identify the limit as `N(0, 1)`.

**What is and is not there.** The contribution is the choice of assertion
class that survives the limit, and the examples. The programs are never run;
`dt` is a device for proofs. Nothing says how fast the discrete meaning
approaches the continuous one, so nothing connects a run at a real `dt` to
the continuous answer. Uniqueness of the limit is shown only case by case.
The proofs are classical throughout (compactness of measures, nonstandard
extensions).

## 2. The area

The paper's parent is Suenaga and Hasuo's `While_dt` (ICALP 2011, the
paper's [3]): the deterministic language, with `dt` a literal infinitesimal
of nonstandard analysis, and a Hoare logic justified by the transfer
principle. The neighbours, by what they take as primitive:

| Line | Primitive | Runs? | Note |
|---|---|---|---|
| `While_dt`, `pWhile_dt` | a step `dt`, limit or infinitesimal | no | programs look ordinary; meaning is classical |
| Differential dynamic logic (Platzer; KeYmaera X) | ODEs inside hybrid programs | no | differential invariants avoid solving; the industrial hybrid-systems prover |
| Exact real computation (iRRAM, AERN, Clerical — the paper's [69]) | reals with a `lim` operator | yes, to any precision | comparison is partial or nondeterministic; Clerical has a Hoare logic |
| Constructive analysis in type theory (CoRN; Makarov and Spitters, Picard in Coq, ITP 2013) | reals with moduli | yes, by evaluation | an ODE solution is a term that computes |
| Validated numerics (Taylor models; Immler's verified ODE solver in Isabelle, the Lorenz attractor) | interval or Taylor-model enclosures of the flow | yes, fast | discrete machine arithmetic with a proved enclosure of the continuous truth |
| Verified numerical programs (Boldo et al., the wave equation in C) | a float program and a PDE | yes | method error and rounding error bounded separately, then added |
| Domain-theoretic ODEs (Edalat and Pattinson) | Picard on interval-valued functions | yes | the same idea as validated numerics, as semantics |
| Functional reactive programming | behaviours `Time → A` | sampled | continuous-time *semantics*, discrete execution, no error statement |

Two observations organise it.

1. **The limit and the modulus.** Classical work takes the limit and loses
   the program (`While_dt` cannot run an infinitesimal; `pWhile_dt` gets a
   set). Constructive and validated work keeps a *rate*: how small `dt` must
   be for a wanted accuracy. With the rate the continuous meaning is a
   computable real, and the rate is exactly the bridge between a run at a
   real `dt` and the continuous answer. Heather's analysis library already
   takes this side: `Converges` and `CauchySeq` carry their moduli as data
   (`lib/std/analysis/sequence.hthr`).

2. **Guards.** `while (x < 1)` on a real is not decidable, and that is not a
   technicality: it is why hybrid systems have Zeno behaviour and grazing,
   why the paper needs its variable classes and gets sets of limits
   (reflection and absorption are discontinuous in the path), and why exact
   real languages have nondeterministic or partial comparison. Any honest
   continuous-time language meets it. The constructive answers are
   cotransitivity (`a < b` gives `a < x ∨ x < b`: a guard with a tolerance)
   and treating guards as opens, which is where the locale work comes in
   (§5.4).

## 3. What "literally programming in continuous time" can mean here

Three readings, in increasing ambition.

**(A) `dt` programs with a limit.** The paper's reading, made constructive.
A program is an ordinary Heather function of a step, `p : Step → S`. Its
continuous meaning is `lim p`, given with a modulus, so it is a `CReal` (or
a point of a complete space) that evaluates. No new syntax, no new kernel
feature: `for` and `while` loops over `Rat` or `CReal` state already exist.
What is new is a small vocabulary (a program family, its limit, its *order*
of convergence) and theorems that produce the modulus for classes of
programs rather than one at a time.

**(B) Continuous objects as values.** Time is a `CReal`; a trajectory is a
function with a modulus of continuity; `integral`, `solve` (an ODE), `flow`
are library functions that return such values. A program composes them and
is run by asking for a precision. This is CoRN's and exact-real
computation's reading. (A) is how (B)'s operators are *implemented*:
`integral f` is the limit of the `dt` program `x += f(t)·dt`, and `solve` is
the limit of Euler's (or Picard's iteration). So (A) is the first layer, not
an alternative.

**(C) Hybrid programs.** Flows interrupted by discrete jumps, with guards on
real state, as interaction trees or transition systems whose steps carry a
duration. This is where interaction trees, simulations and effects meet the
reals, and where the guard problem has to be faced. It needs (B).

The paper's Hoare logic itself is not something to port. In a proof
assistant the "discrete logic" is ordinary theorems about the function `p`,
with `dt` a parameter, and Transfer is one lemma (§4.2).

## 4. The probes

`lib/_tests/std/analysis/continuous_time_tests.hthr`, all at `Rat` so that
everything runs by kernel evaluation. No library or compiler change was
needed.

### 4.1 A deterministic program, run and proved

`t' = 1`, `x' = 2t` as the loop `x += 2t·dt; t += dt`, written twice: as
a `while` over `let mut` state (`fall_loop`) and as the recursion the proofs
read (`fall_run`). Both run by kernel evaluation: four steps of 1/4 give
3/4, eight of 1/8 give 7/8. The loop invariant, that `x - t² + t·dt` is
conserved (`fall_invariant`), is a three-line induction with `ring`, for
every `dt` at once; with the clock (`fall_clock_spec`) it gives the
program's exact value at resolution `k` (`k + 1` steps of `T/(k + 1)`):

    fall_at(T, k) ≈ T² - T²/(k + 1)          (fall_at_spec)

One thing the loop form shows at once: the paper's guard `t < T` cannot be
the Heather loop's guard as written. A `while` needs a `decreases`, and the
measure of a clock guard is the number of steps left, `⌈(T - t)/dt⌉`, which
exists because `dt` is positive and the field Archimedean. The probe counts
steps instead. A step-program library should supply that measure once
(§5.4 has the harder version of the same question).

### 4.2 Into continuous time

`fall_continuous(T): Converges(λ k => fall_at(T, k), T * T)`. The proof
term is the modulus: from a tolerance it computes the resolution that meets
it. `dt_linear_error` is the reusable step (a family whose error is
`c·dt` converges), over `Converges::add`/`scale` and the Archimedean
property.

The paper's Transfer rule is `dt_transfer_le`, a one-line corollary of the
existing `Converges::le`: a closed bound that holds of the program at every
step holds of its limit. "Wasserstein-closed assertion" becomes "a relation
the limit lemmas preserve": `≤`, `≈`, and their images under uniformly
continuous maps (`UnifContOn::converges`), which the library already has.

### 4.3 Back out, more accurate than any run

Knowing the *form* of the error is worth more than the limit alone. The
error above is exactly linear in `dt`, so

    2·fall_at(T, 2k + 1) - fall_at(T, k) ≈ T²        (fall_richardson)

at every resolution: two coarse runs, each off by a quarter of the answer or more,
combine to the continuous answer exactly (`fall_richardson_runs`: 9 from a
two-step and a four-step run at `T = 3`). This is Richardson extrapolation,
and here it is a theorem about a program rather than a numerical habit. In
general the error is `c·dt + O(dt²)` and the combination is `O(dt²)`
accurate: the claim needs an error *expansion* in `dt` with a certified
remainder, which is the object [[certified-expansions]] already plans.

### 4.4 The paper's Program 1

`walk_expect(g, h, x, n)`: the expectation of a test function `g` after
`n` steps of `±h` from `x`, `h = √dt`. This is the discrete semantics of
the Brownian program read through a test function, and it runs (sixteen
paths at `dt = 1/4` give `E[x⁴] = 5/2`). The paper's first results are
short inductions with `ring`:

- `walk_mean`: `E[x] = x₀`, the invariant `{E[x] = 0} … {E[x] = 0}`;
- `walk_second`: `E[x²] = x₀² + t`, exact at every `dt`;
- `walk_fourth`: from the origin `E[x⁴] = 3t² - 2t·dt`. No run has the
  Gaussian's fourth moment; the gap is linear in `dt`.

At time 1 (`walk_unit`, steps of `1/(j + 1)`): the variance is 1 at every
resolution, and `walk_unit_fourth_continuous` proves the fourth moment
converges to 3, the Gaussian's `(4 - 1)!!`, again with its modulus. The
paper obtains this through its approximate-invariant rule and the Wasserstein
machinery; here the exact discrete value makes it arithmetic.

What the probe does not do is say that the limit *is* a Gaussian measure.
§5.3 says what would.

## 5. Assessment

### 5.1 What Heather has, and what is missing

| Need | State |
|---|---|
| Limits with moduli, algebra and order of limits | `sequence.hthr`: done, generic over an ordered field |
| A complete carrier that computes | `CReal`, `CauchyComplete`, `CReal::lim` |
| Lipschitz, uniform continuity, derivatives, mean value inequality | `real_fn.hthr` |
| A fixed-point theorem | `Contraction::fixed_point`, for points of the field only |
| `exp`, `log`, `sqrt` | present at `CReal` |
| Running a real to a precision | `CReal::at`; interval enclosures; floats with error-free transformations |
| Integration | **missing** entirely |
| Function spaces as complete spaces (Picard), discrete Grönwall (Euler) | **missing** |
| Order of convergence, error expansions in a step | **missing** ([[certified-expansions]], [[asymptotic-relations]] open) |
| Taylor models | [[taylor-model-enclosures]] open |
| Probability | [[finite-probability]] open; measure not started |
| Durations on transition steps, hybrid traces | nothing; `labelled_transition.hthr` is the place |
| Native code over reals or floats | `runtime fn` holds machine words only |

### 5.2 The deterministic side is cheap and fits

Reading (A) costs a library round or two and uses what exists. The order:

1. **Step families and their order.** A record for "a family indexed by
   resolution, with limit `l` and error at most `C·dtᵖ`", transfer lemmas,
   Richardson as a theorem (order `p` to order `p + 1` given the leading
   coefficient exists). Small; generic over `OrderedField`.
2. **Integration as the first `dt` program.** `x += f(t)·dt` for uniformly
   continuous `f` is Cauchy in `dt` with a modulus read off `f`'s; its limit
   is the integral. Linearity, monotonicity, the fundamental theorem against
   `DerivOn`. Everything later needs it (Picard, expectation against a
   density), and `math-reals` has no integration issue yet.
3. **Euler for a Lipschitz field.** Discrete Grönwall, the `O(dt)` bound,
   so `solve(f, x₀, T) : CReal` exists, is unique, and runs. The acceptance
   probe: the Euler program for `x' = x` has continuous meaning
   `CReal::exp`. Makarov and Spitters did Picard in Coq over CoRN; Euler
   with Grönwall is the more elementary route and matches the `dt` reading.

After (3) the sentence "a program in continuous time" has a library meaning:
a term built from `integral` and `solve`, with a `CReal` value and, through
(1), a statement of how wrong any given discretisation of it is.

### 5.3 The stochastic side: cheap up to moments, expensive beyond

The discrete meaning of a surely terminating `pWhile_dt` program is finitely
supported, so [[finite-probability]] (expectation as a state on test
functions) is the whole of its discrete semantics, and it computes. Moment
statements transfer by sequence limits alone, as §4.4 shows.

The expensive part is the paper's actual semantics: measures on `ℝⁿ`, weak
or Wasserstein convergence, and existence of limits by tightness, which is a
compactness argument with no modulus. Heather has no measure theory and
should not start one for this.

There is a route that avoids it and lands on a milestone the roadmap
already has. `docs/surveys/wick-survey.md` §3.4 takes a Gaussian to be *a state on a
polynomial algebra* defined by Wick's rule ([[ml-gaussian-states]]). The
paper's headline result, `E[xⁿ] = (n - 1)!!` for even `n`, says exactly that
the random-walk states converge, on every polynomial, to that state. So
"Brownian motion at time `t` is the limit of its `dt` program" can be stated
and proved as convergence of states on polynomials, with a rate (the gap is
`O(dt)` on each monomial), and no measure. That is a natural first customer
for `finite-probability` and a test of the Gaussian-state interface, and it
is as far as the stochastic side should go for now.

### 5.4 Guards, hybrid programs, and the locale thread

Reading (C) is where this stops being a library round. Three things are
known in advance:

- A guard on a real is a tolerance (`Rat::lt_cotrans`, `PseudoOrder`
  cotransitivity) or an open. A while-loop over a real guard is therefore a
  nondeterministic or partial program near the boundary. `partial fn` and
  `CoTree` already give the partiality; the nondeterminism wants a choice
  event.
- Event detection ("the first time `x` reaches 1") is root finding. The
  exact IVT in `closed_interval.hthr` needs local non-constancy for the same
  reason hybrid systems need transversality: a trajectory that grazes the
  guard has no computable crossing time.
- The localic reals ([[localic-real-numbers]]) are the setting in which
  "semidecidable guard" is a first-class notion (an open of the locale) and
  in which compactness of `[a, b]` holds without choice, which is what
  uniform statements over a time interval lean on. If hybrid programs are
  wanted, their guards should be designed with that thread and not before
  it.

A cheaper intermediate that is already expressible: a transition system
whose labels carry a duration, with the `dt` program and the `dt/2` program
related by a simulation up to an error relation. `transition.hthr` has the
diagrams; what it lacks is a metric on states, so this waits for (1).

### 5.5 Native compilation

The chain a compiled continuous-time program wants is

    continuous meaning : CReal
        ← (order of convergence, §5.2)   dt program over Rat/CReal
        ← (rounding error, float library) the same loop over floats
        ← (compiler certificate)          x86

Each arrow is a different kind of theorem, and Boldo's wave-equation proof
is the precedent for adding the first two. Heather has the third for
machine words, the float library for the second's vocabulary (error-free
transformations, rounding to reals), and nothing yet joining them:
`runtime fn` has no float or fixed-point type. So native continuous-time
programs are downstream of floats-in-`rt`, which is its own milestone
question and not something this area should pull forward.

The part of the vision note that does connect now: "facts as side-proofs
the compiler finds". A loop proved to have continuous meaning `T²` with a
known error is a loop the compiler may replace by a cheaper computation
with a smaller error, with the theorem as the licence. That is the same
shape as any certified rewrite, and needs no new compiler concept.

### 5.6 Utility against the naive method

The naive method is to write the float loop and shrink `dt` until the answer
stops moving. For getting numbers it wins almost always, and §5.2 should be
read with that in mind (discussed with Minus, 2026-11-10):

- A-priori bounds do not choose a step. The Euler bound carries a factor
  like `e^(L·T)`, so the proved modulus asks for a step far smaller than is
  needed. Bounds tight enough to act on are a-posteriori enclosures
  (intervals, Taylor models), a heavier project.
- Exact execution is slow. The probes run at `Rat` by kernel evaluation and
  the denominators grow with every step.
- Extrapolation and closed forms are what a numerics library or a computer
  algebra system already does, unproved; the proof is rarely what was
  missing.

Comparing a float program with the same algorithm over the reals is the
obvious case and predates the paper. What the `dt → 0` layer adds on top:

1. The real algorithm is still discrete: "Euler at `dt = 0.01` over ℝ" is a
   specification that names its own method. With the continuous meaning as
   the specification, the step and the scheme become a choice, every
   discretisation is a refinement of one meaning, and a setup may pick one
   to meet a tolerance from two budgets (truncation and rounding). This is
   precision selection one level up, and the only part that is programming.
   It is worth something only with tight a-posteriori bounds.
2. Some facts are exact only in the limit and calculus is simpler than
   sums: reason in the continuum, return with an `O(dt)` correction. A proof
   convenience.
3. The paper's own direction, continuous facts by discrete program
   reasoning, is a cheap route to some continuous mathematics. A proof
   technique.

### 5.7 Verdict

- **The paper**: read for its idea (ordinary programs in a step, meaning by
  limit, proofs transferred from the discrete), not for its logic. Its
  semantics is classical where Heather's library is constructive, and the
  constructive version is strictly more useful: it runs and it carries the
  rate.
- **The deterministic area**: fits the library, but by §5.6 it has no
  customer beyond integration, which `math-reals` needs anyway
  ([[riemann-integration]]). The rest is parked until floats reach `rt` and
  tolerance-driven discretisation has a use: [[step-families-and-order]],
  [[euler-lipschitz-ode]].
- **The stochastic area**: one targeted result (random-walk states converge
  to the Gaussian state), filed as [[random-walk-gaussian-state]], behind
  `finite-probability` and `ml-gaussian-states`. No measure theory.
- **Hybrid programs and a surface for continuous time**: not yet. They
  depend on the guard question, which belongs with the localic reals, and
  any syntax is Minus's design call once (1)–(3) show what programs people
  actually write.
