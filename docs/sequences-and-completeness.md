# Sequences, limits and completeness over an ordered field

Round note for `lib/std/analysis/sequence.hthr` and
`lib/std/analysis/real_complete.hthr` (issue
[real-completeness-interfaces](../issues/real-completeness-interfaces.md),
milestone `math-reals`). It records what the round built, how the
completeness notions relate constructively, and what comes next. The
analysis layers above it are `docs/analysis-foundations-design.md`; the
Cauchy reals below it are `docs/creal-completeness-round.md`.

## 1. What is built

Everything is stated once over a section's `K: OrderedField(≈, <, <=, +,
*)`, as `real_fn.hthr` is, so it reads at `Rat` and at `CReal` alike.

**Predicates, with their moduli as data.** A sequence is a plain `Nat → K`.

- `Converges(xs, l)`: each `ε > 0` has an `N` with `|xs(n) - l| <= ε` for
  every `n >= N`.
- `CauchySeq(xs)`: each `ε > 0` has an `N` with `|xs(m) - xs(n)| <= ε` for
  every `m, n >= N`.

`∃` is a Σ in Heather, so a proof is a modulus: the index can be computed and
fed to the next estimate. Bounds are `AbsLe`, never a decided `abs`. Only
indices are compared (`Nat::max`, `Nat::le_total`). Each part of a sum gets
its share of `ε` (`OrderedField::half`, `shrink`), and no minimum of two
tolerances is ever taken.

**Limits.** `Converges::const`, `respects` (`≈` termwise and at the limit),
`unique`, `add`, `neg`, `sub`, `scale`, `mul` (via `eventually_bounded`),
`le` (termwise `≤` passes to the limits), `squeeze`, and `cauchy`
(a convergent sequence is Cauchy). `CauchySeq::converges_of_cluster`: a
Cauchy sequence converges to any point it keeps returning near.

**Continuity through sequences.** `UnifContOn::converges` and
`LipschitzOn::converges` carry a limit inside the domain to the limit of the
images. The modulus of `f` at `ε` is the tolerance asked of the sequence.

**Powers.** `OrderedField::npow_{zero,succ,nonneg,le_one,add,antitone}`, then
Bernoulli's inequality in the divided form `cⁿ·(1 + n·(1 - c)) <= 1`
(`npow_bernoulli`), and `npow_small`: `cⁿ` falls below any `ε > 0` for
`0 <= c < 1`, from Bernoulli and the Archimedean field law.

**Cauchy completeness as a capability.** This is
`class CauchyComplete<A>(≈, <, <=, +, *) extends OrderedField`, with one field
`cauchy_limit`: every Cauchy sequence has a limit, given as data. The field's
type spells `CauchySeq` and `Converges` out, because a class body cannot name
the section's predicates. `CauchyComplete::limit`, `::converges` and
`::limit_unique` read it back in their terms.

**The CReal instance** (`real_complete.hthr`). `CReal::complete` takes
sequences at the reals' own rate `2^-m + 2^-n`. A generic Cauchy sequence is
read at its modulus, `ys(k) = xs(N(2^-k))`. Two such terms are both past the
smaller of the two indices (`Nat::le_total` picks which), so `ys` is regular
(`CReal::cauchy_regular`). Its diagonal limit `CReal::lim` is the limit of
`xs` itself: a term past `N(2^-(k+1))` is within `2^-(k+1)` of `ys(k+1)`,
which is within `2^-(k+1)` of the limit, and `2^-k <= ε` for some `k`
(`CReal::pow2_below`, from `pos_gap`). Nothing is chosen, and the limit's
terms evaluate.

**The consumer: the contraction mapping theorem.** A `Contraction(f, c)` has
`0 <= c < 1` and `|f(y) - f(x)| <= c·h` whenever `|y - x| <= h`. Its orbit
`Contraction::orbit(f, x, n)` moves by at most `cⁿ·D` at step `n`
(`Contraction::step`, where `D` bounds the first step). The tail past `n`,
of length `k`, is within exactly `cⁿ·D·(1 - cᵏ)·R`, with `R` the reciprocal
of `1 - c` (`Contraction::tail`). That form is chosen because its induction
step is a ring identity given `(1 - c)·R = 1`, so no geometric sum is ever
formed. So the orbit is Cauchy over any ordered field (`Contraction::cauchy`).
In a `CauchyComplete` field its limit is a fixed point
(`Contraction::fixed_point`, which uses continuity and the shifted orbit),
and there is only one (`Contraction::fixed_unique`, which needs no
completeness). `Contraction::affine` gives the first instances.

The probes in `lib/_tests/std/analysis/sequence_tests.hthr` cover four
things. `Converges` is not vacuous (`0 ↛ 1`). An orbit of `x ↦ x/2 + 1` is
Cauchy at `Rat`. The same map's fixed point at `CReal` is found and shown to
be `2`. The theorem is refused at `Rat`, which has no `CauchyComplete`
instance (`// expect-error`).

Proof-engineering notes, for later rounds:

- `linarith` does not unfold `npow`. Hand it `OrderedField::npow_succ` /
  `npow_zero` as facts, and spell a goal whose power sits inside a product
  with the power's value (`1 * (…)`, `(t * c) * (…)`).
- At a concrete carrier, ascribe the two halves of a generic `AbsLe` with the
  carrier's spelling (`let lo: (-e <= …) = linarith(…)`). Otherwise
  `linarith` reads the dictionary's `inv` and `≤` unreduced.
- Chained witnesses (`npow_small` over a `shrink` over an `archimedean`) made
  `Contraction::cauchy` run past the CPU rail. The `*_close` pattern
  (`Contraction::cauchy_close`, `npow_small_close`,
  `fixed_unique_close`) fixed it, at a cost of tens of thousands of kernel
  steps per declaration (`docs/proof-patterns.md`).
- `n ≥ N` becomes `n = N + k` through `Nat::le_add` and `rewrite`, so an
  induction can run on `k` (`npow_antitone`, `Contraction::close`).
- A theorem stated over a numeral starting point (`orbit(…, 0, n)`) fixes
  the section's carrier at `Nat`. Take the point as a parameter instead.

## 2. The completeness notions, kept apart

The issue asks for orthogonal capabilities, each with one consumer and one
carrier expected not to inhabit it. Here is how they relate in Heather's
setting: constructive, with `∃` as data, and no countable choice assumed.

| Notion | Statement | Inhabited by | Not by | Status |
|---|---|---|---|---|
| Regular-sequence completeness at a fixed rate | every `xs` with `\|xₘ - xₙ\| <= 2^-m + 2^-n` converges at that rate | `CReal` (`CReal::complete`) | `Rat` | built, CReal-only |
| Cauchy completeness with a modulus | `CauchyComplete` | `CReal` | `Rat` | **built** |
| Sequential completeness, modulus only asserted | Cauchy as `∀ε. ∥∃N …∥` | `CReal` *with* countable choice | — | not stated |
| Order completeness at located sets | a nonempty, bounded-above, upper-located set has a supremum | `CReal` (by bisection) | `Rat` | **built**, equivalent to the row above (§4) |
| Classical least-upper-bound | every nonempty bounded-above set has a supremum | nothing constructive | `CReal` | not a capability |
| Monotone convergence | every bounded monotone sequence converges | nothing constructive | `CReal` | not a capability |

How they connect:

- **Fixed rate and modulus are equivalent** once the modulus is data. One
  direction is `CReal::cauchy_regular`: read the sequence at `N(2^-k)`. The
  other is immediate, since a regular sequence has the modulus `k ↦ k + 1`.
  So `CauchyComplete` is the rate-free statement of the same strength.
- **Countable choice sits between the modulus and the mere existence of
  one.** If Cauchy is stated with a truncated `∃N` (`∥∃N…∥`), extracting a
  modulus is AC(ℕ,ℕ). With Heather's Σ-`∃` the two coincide, so the truncated
  form would only be worth stating for a client that produces truncated
  evidence. None exists yet.
- **Order completeness needs locatedness.** A supremum exists constructively
  only for a set whose upper bounds are located: for `a < b`, either `b` is
  an upper bound or some element exceeds `a`. With that disjunction as data,
  bisection builds a Cauchy sequence of upper bounds with a modulus. So
  `CauchyComplete` plus Archimedean gives located suprema, with no choice,
  and the converse holds too, so the two rows are one capability (§4).
  The unrestricted least-upper-bound principle implies LPO (Bishop–Bridges),
  so no constructive carrier inhabits it, `CReal` included. Monotone
  convergence is equivalent to LPO in the same way.
- **Dedekind and Cauchy reals.** Located Dedekind cuts are Cauchy reals.
  Without countable choice the Dedekind reals can be strictly larger. That
  comparison is [located-dedekind-reals](../issues/located-dedekind-reals.md)
  and [real-presentation-comparison](../issues/real-presentation-comparison.md),
  not this capability.

## 3. Next

- **`Rat` is not Cauchy complete**, as a `¬` theorem rather than a missing
  instance ([rat-not-cauchy-complete](../issues/rat-not-cauchy-complete.md)).
  The sequence `2.root_floor(n)` is Cauchy at `Rat`
  (`Rat::root_floor_regular`). A rational limit `l` would have
  `l·l ≈ 2` (`Converges::mul`, `Converges::le` against `root_floor_spec`),
  and `num² = 2·den²` has no solution with `den > 0`. That last fact is
  descent over `Nat`, and the parity lemmas are in `nat.hthr`.
- **Series**: partial sums, `Summable`, the geometric series and comparison
  with a tail modulus. These come before
  [power-series-evaluation](../issues/power-series-evaluation.md), and the
  orbit's tail bound above is already a geometric estimate.
- **A contraction on a closed domain** (a domain that keeps its limits), the
  form Newton's lemma needs locally
  ([valued-rings-and-newton](../issues/valued-rings-and-newton.md)).

## 4. Located suprema

`lib/std/analysis/supremum.hthr` (issue
[order-completeness-located-sup](../issues/order-completeness-located-sup.md)).
A set is a predicate `S: K → Type`, and its supremum carries its
approximation as data:

- `UpperBound(S, b)`: every element of `S` is `<= b`.
- `IsSup(S, s)`: `s` bounds `S`, and each `ε > 0` has an element of `S`
  above `s - ε`.
- `UpperLocated(S)`: for `a < b`, either `b` bounds `S` or some element is
  above `a`, as a disjunction a proof branches on.

A supremum is below every upper bound (`IsSup::le_upper`), so it is unique up
to `≈` (`IsSup::unique`), and it moves along `≈` (`IsSup::respects`).
Locatedness is necessary as well as sufficient: a set with a supremum is
upper located (`IsSup::located`), since cotransitivity places `s` against
`a < b`.

**The bisection.** Stage `n` (`Bisection(S, c, w, n, a, b)`) has `b`
bounding `S`, an element of `S` above `a`, and width `b - a ≈ cⁿ·w`. One
step (`Bisection::step`) cuts at `a + d < b - d` with `d = t·(b - a)` and
`2t < 1`, asks the located disjunction there, and keeps `[a, b - d]` or
`[a + d, b]`. Either way the width becomes `(b - a)·(1 - t)`. `t = 1/4`
(`Bisection::quarter`), so `c = 3/4`. The stages are a plain recursion over
the disjunction (`Bisection::run`). The proof needs no nesting of the
intervals: any stage's lower end is below any stage's upper end, because the
element above the one is below the other (`Bisection::stage_lt`). So two
upper ends past `N` are within the larger width, which is at most `cᴺ·w`,
and the upper ends are Cauchy with the modulus `npow_small` gives
(`Bisection::cauchy`). In a `CauchyComplete` field their limit bounds `S`
(each upper end does, and `Converges::le` passes it to the limit), and an
element of a late stage is above `s - ε` (`Bisection::limit_approx`). That
is `CauchyComplete::located_sup`, and `CReal::located_sup` reads it at the
reals.

**The capability.** `class OrderComplete<A>(≈, <, <=, +, *) extends
OrderedField` has one field, `located_sup`, spelled out as `CauchyComplete`'s
is; `OrderComplete::sup` and `::is_sup` read it back. `CReal` inhabits it
(real_complete.hthr). `Rat` does not, and the probe
`rat_ray_sup_refused` in `lib/_tests/std/analysis/supremum_tests.hthr` holds
that refusal.

**Equivalent to Cauchy completeness.** The converse is
`OrderComplete::cauchy_limit`: a Cauchy sequence converges to the supremum
of the points it eventually stays above (`OrderComplete::EventuallyBelow`).
Past an index `N` where the sequence stays within `δ`, `xs(N) - δ` is
eventually below it and `xs(N) + δ` bounds every point that is
(`below_at`, `bound_at`). Those two facts at `δ = (b - a)/4`, with
cotransitivity placing `xs(N)` against `a + δ < b - δ`, make the set upper
located (`below_located`), and at `δ = ε/2` they put the supremum within `ε`
of every late term. So over an ordered field with the Archimedean law (which
`OrderedField` carries) the two capabilities coincide. They stay two
classes because each is the natural statement for a different consumer:
limits for the contraction mapping theorem and series, suprema for extrema
and the intermediate value theorem.

Proof-engineering notes:

- Each piece of the bisection is a theorem over plain parameters
  (`width_close`, `cauchy_close`, `approx_close`, and the `Bisection::*`
  lemmas that take `t`, `w`, `a0`, `b0` and the first stage as parameters).
  Written as one theorem with the setup in `let`s, the main proof ran past
  8 GiB.
- Calling a theorem whose result type is a definition that unfolds to a Π
  with the Π's arguments merged into one list (`bound_at(xs, d, N, hN, y,
  sy)`) panics the kernel's substitution when the definition was declared at
  a parent class's section
  ([merged-call-through-upcast-panics](../issues/merged-call-through-upcast-panics.md)).
  Bind the result with `let` and apply it.

## 5. Functions on a closed interval

`lib/std/analysis/closed_interval.hthr` (issue
[located-sup-consumers](../issues/located-sup-consumers.md)), the consumers
§4 named. The interval is `I = λ x => Within(<=, a, x, b)` with `a <= b`,
and `f` is `UnifContOn(I, f)` (real_fn.hthr).

**One walk.** Every proof here walks from a point `x` of the interval
towards `b`. Cotransitivity places the length `b - x` left against
`δ/2 < δ`, `δ` the modulus at the `ε` the proof chose. Below `δ`, every
point of `[x, b]` is within `δ` of `x`, so `x` speaks for the rest of the
interval; above `δ/2`, the walk steps to `x + δ/2`, which is still inside
(`Within::step`). The Archimedean property bounds the number of steps
(`OrderedField::archimedean_mul` at `b - a`), and the walk is an induction
on it. So there is no grid and no floor placing a point on it: where a proof
needs to know whether a point `y` lies before or after the step, the goal is
a `≤`, which `StrictOrder::le_by_cases` splits on without a decision. The
issue had sketched a grid with a covering lemma; the walk is that grid read
one point at a time, and the covering lemma becomes the `≤` split.

- **Bounded** (`UnifContOn::bounded`). The walk at `ε = 1`
  (`UnifContOn::steps`, over any convex domain) puts every `f(x)` within
  `n + 1` of `f(a)`, and `|f(a)| <= f(a)² + 1`. This is the bound the product
  and chain rules of real_fn.hthr take as a hypothesis.
- **The image is upper located** (`UnifContOn::located`), as the set
  `ImageOn(I, f, y)`: some `x ∈ I` has `f(x) ≈ y`. For `p < q` with
  `h = (q - p)/2`, cotransitivity at each point of the walk says `p < f(x)`,
  an element of the image above `p` that stops the walk, or `f(x) < p + h`,
  which bounds `f` by `q` within `δ` of `x` (`UnifContOn::located_steps`).
- **The supremum** (`UnifContOn::sup`): in an `OrderComplete` field the
  image, inhabited and bounded, has one, with its approximation as data. A
  maximum, a point where `f` attains it, is not claimed: constructively it
  exists only under further hypotheses.
- **The approximate intermediate value theorem** (`UnifContOn::ivt_approx`).
  With `f(a) <= 0 <= f(b)`, every `ε > 0` has a point of `I` with
  `|f(x)| <= ε`. The walk keeps `f(x) <= ε/2`, and cotransitivity at each
  point says `-ε < f(x)` (so `|f(x)| <= ε`, found) or `f(x) < -ε/2`, and then
  `f` at the next point is `<= 0`. The walk cannot end that way, since within
  `δ` of `b` the second case would put `f(b) < 0`. It spends no completeness:
  the probe `rat_sqrt_two_approx` reads it at `Rat`.

**The exact theorem, and its hypothesis.** An exact root needs more than
continuity constructively: for a function that lingers at `0` the root
depends on the sign of an undecided real. The hypothesis is *local
non-constancy* (`LocallyNonconstOn(I, f)`): every `x < y` in `I` and every
value `c` have a `z ∈ [x, y]` with `f(z)` apart from `c`. It is the general
constructive form (Bridges–Richman). A strictly increasing function
(`StrictMonoOn`) has it, since cotransitivity places `c` against
`f(x) < f(y)` (`StrictMonoOn::nonconst`), and so does a polynomial that is not
constant: a finite difference of its degree is a nonzero constant, and a
positive sum has a positive term. The probe `cubic_nonconst` does this for
`x³ - x`, whose third difference at step `h` is `6h³`.

`UnifContOn::ivt_nonconst` proves the theorem in a `CauchyComplete` field for
`a < b` (`UnifContOn::ivt` is its strictly increasing case). It is a
bisection like §4's. Stage `n` (`RootStage`) is `[l, r] ⊆ [a, b]` with
`f(l) <= 0 <= f(r)`, `l < r` and width at most `cⁿ·w`. One step asks local
non-constancy for a `z` in the middle `[l + d, r - d]` (`d = t·(r - l)`,
`t = 1/4`) with `f(z)` apart from `0`, and keeps `[z, r]` when `f(z) < 0` or
`[l, z]` when `0 < f(z)`. Either way the width falls by `1 - t`
(`RootStage::cut_width`), and the new stage lies inside the old. Nothing
outside the stages orders their ends, so the nesting is proved: stage
`m + k` inside stage `m` by induction on `k` (`RootStage::nested_add`), and
`Nat::le_add` turns any `N <= n` into that shape (`RootStage::nested`).
Every lower end past `N` then lies in stage `N`, whose width bounds their
distances, so the lower ends are Cauchy. Their limit `z` is in `[a, b]`, and
continuity at a late stage gives `f(z) <= ε` from its lower end and
`f(z) >= -ε` from its upper one.

The probes find `√2` (`creal_sqrt_two`, strictly increasing) and a root of
`x³ - x` on `[-2, 2]` (`creal_cubic_root`, not monotone there); at `Rat` the
same call is refused for want of the `CauchyComplete` instance
(`rat_sqrt_two_refused`).

Proof-engineering notes:

- `RootStage::step` is a `fn` whose body is only the choice: the cut points
  and both outcomes are theorems over plain parameters (`cut`, `keep_left`,
  `keep_right`). Written as one theorem with its proofs in `let`s, the
  kernel ran out of fuel checking `nested_add`, whose conversions unfold
  `run(Succ(j))` to `step(…)`.
- `RootStage::limit_nonneg` first stated the final estimate inline, and its
  kernel check was an order of magnitude past the rest of the module; the
  estimate moved into `RootStage::nonneg_close`, over plain parameters, as
  §4's `*_close` lemmas did.
