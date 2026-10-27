# Foundations for analysis: finite sums, asymptotics, expansions

Status: design and survey, 2026-10-27. No code lands with this note; the
rounds it orders are filed as issues (§12). It answers part of
`issues/big-operator-semantics.md` (the finite case, §3) and the design
question in `issues/real-functions-and-derivatives.md` (which derivative,
§6), and it proposes a route to the laws in
`issues/elementary-functions-at-reals.md` (§7).

## 1. The thesis

The usual road through analysis treats Taylor series as the thing the
library is for. Define limits, then derivatives, then iterated derivatives,
then Taylor's theorem, and then define `exp`, `sin` and `cos` as their
series. Every later result goes back through that chain. Heather's current
`exp`/`sin`/`cos` (`lib/std/num/float/elementary.hthr`) already follow it.
They are series with a ratio bound, and their laws are stuck because each
law needs analysis that does not exist yet.

The proposal is to make Taylor series one instance of a more general
object. Three ingredients are worth founding separately, because each
already has a good theory of its own:

1. **Finite algebra.** `∑` and `∏` over finite index sets, difference
   calculus, polynomials, and truncated and formal power series. All of it
   computes at `Rat` and all of it is ring identities, so `ring` (and,
   modulo `≈`, PR #219) does most of the proving.
2. **A way to say "small", with the witness as data.** These are
   neighbourhood bases indexed by `Nat`, an "eventually" whose threshold is
   a value, and Landau's `O`, `o` and `~` with their constants and moduli
   written in. Heather's reals already use this shape three times without
   naming it (§2).
3. **The coupling, which is a certified expansion.** A finite part from (1)
   plus a remainder bounded by (2): `f = ∑_{k<N} c_k φ_k + O(φ_N)`. An
   expansion stands to a function germ as an `Interval` stands to a number.
   It is finite data that encloses the object with a certified error, and
   arithmetic on expansions is `O`-arithmetic, just as interval arithmetic
   widens its bounds.

On top of those three, the familiar results become constructions rather
than foundations:

| Result | How it falls out |
|---|---|
| Derivative | the coefficient of `h` in a first-order expansion of `f(x + h)` (uniform: Bishop's derivative) |
| Sum, product and chain rules, Faà di Bruno | ring identities in the jet algebra (1), plus one remainder lemma per operation (2) |
| Taylor's theorem | relates order-`N` expansions to iterated derivatives. It is a theorem and defines nothing |
| `exp(a+b) = exp(a)·exp(b)` | the binomial theorem coefficientwise (1), plus "evaluation is a ring homomorphism" on a disc (§7) |
| `sin² + cos² = 1` | formally, `D(s² + c²) = 0` with constant term 1, so the series is `1` by its coefficients. Then evaluate |
| Limits, continuity | `f - L = o(1)` at an approach (2) |
| Stirling, harmonic numbers | divergent asymptotic expansions (3) at `n → ∞`. Here a Taylor-first library has nothing to say (§8) |
| Float error analysis | first-order perturbation in `u`. `Format::gamma_add` is already `O`-arithmetic (§9) |
| Perturbation series | formal Newton lifting in `A[[ε]]` (1), justified by a contraction with rates (§9) |
| Transseries | (1) with the monomial monoid `ℕ` replaced by an ordered group of log-exp monomials (§10) |

This is not a new idea in mathematics. It is Bourbaki's and Dieudonné's
"développements limités", Bishop's moduli, the algebra of Poincaré
asymptotic expansions, the Taylor models of validated numerics, and the
grid-based transseries of van der Hoeven. What is particular to Heather is
that all four can share one set of finite records. In a constructive kernel
the remainder's constants and thresholds are data, and that collapses the
difference between "asymptotic" and "validated".

## 2. What Heather has to build on

On master `6c4a0e4`, with PR #219 open:

- **Folds.** `MonoidRel::fold`, `MonoidRel::fold_append` and
  `CommMonoidRel::fold_map_op` (`lib/std/algebra/semiring.hthr`) fold a list
  in a monoid modulo a relation. Because the semiring layers tag the
  product monoid as `multiplicative`, one commutative-monoid theorem serves
  both `Σ` and `Π`, which `fold_map_op`'s comment already says. `ListAlg`
  and `TreeAlg` give initial-algebra folds. `Fin(n)` and `Nat::fact`/`pow`
  exist.
- **Scalars.** `Rat` has a complete order theory, `abs` and `inv_succ`.
  `CReal` is regular Cauchy sequences at the rate `1/(n+1)`
  (`lib/std/num/creal.hthr`), with `≈` as a setoid, order, inverse, and
  completeness (`CReal::Regular`, `CReal::Limit`, `CReal::lim`,
  `CReal::complete`). The classes run `OrderedField` over `CommRing`, with
  `of_nat` and `recip`. `CommRingOfInt` and `ring` at `≈` are in #219.
- **Enclosures.** `Interval` over `Dyadic`, `Interval::HasReal`, and
  `RealExpr` with `by intervals()` at `Rat` and `CReal`
  (`lib/std/num/float/interval.hthr`, `creal_interval.hthr`).
- **Series.** `Series { first, ratio, start, small }`
  (`lib/std/num/float/series.hthr`) has the partial sums `Series::sum`, the
  tail estimate `Series::tail`, geometric decay `Series::decay`, the limit
  `Series::real`, and an enclosure. `exp`, `sin` and `cos` are defined at
  rationals by their ratios.
- **Float error.** `Format::gamma` and `gamma_add`
  (`lib/std/num/float/error.hthr`) state `γ_m + γ_n + γ_m γ_n ≤ γ_{m+n}`.

Some observations from that inventory:

1. **`Series::sum` is a hand-rolled finite sum.** It is `match k { Zero =>
   0, Succ(i) => s.sum(i) + s.term(i) }`, which is exactly the range sum of
   §3. `Series::tail` is a telescoping identity fused with a geometric
   majorant estimate.
2. **"Eventually, with the threshold as data" is already written three
   times.** `CReal::Same` is `(k) → ∃ start, (n) → start <= n → |x_n - y_n|
   <= 1/(k+1)`. `regular` is the same bound in uniform form, and `Series`
   has its `start`. Each copy has its own index arithmetic. This is the
   asymptotic layer of §5, unnamed.
3. **The laws of `exp` are blocked on a finite identity.** The `n`-th term
   of the Cauchy product of the `exp` series at `a` and `b` is
   `∑_{i+j=n} a^i/i! · b^j/j! = (a+b)^n/n!`, which is the binomial theorem.
   The only analysis left after that is the tail of a product of two
   geometrically dominated series.
4. **Float error analysis already does `O`-arithmetic.** `gamma_add` is the
   statement that `(1+θ_m)(1+θ_n) = 1+θ_{m+n}`, with second-order terms
   absorbed. It is perturbation theory in `u` to first order, with explicit
   constants.

## 3. Layer A: finite sums and products

**Semantics.** This takes route 2 of `big-operator-semantics`: generic
finite folds over a commutative monoid modulo its relation. Integration is
separate, and it is defined later as a limit of finite sums (§11) rather
than as integration against counting measure. The counting-measure
unification stays open for measure theory. A finite sum is what the
integral of a simple function reduces to, so this layer is a prerequisite
on either route, and nothing here closes that route off. The
expected-type-directed selection of an operator (route 4) is not needed. A
sum over a finite index set has one meaning, and the domain of the index
selects the fold, not the carrier of the summand.

**The core is the range sum**, defined by recursion on `n` so that it
computes structurally, the same way `Series::sum` does:

```heather
// Sketch. `A.unit` is the monoid's unit, as in MonoidRel::fold.
fn MonoidRel::range<A: MonoidRel(≈, op)>(op as ∙: A → A → A, n: Nat, f: Nat → A) → A {
    match n { Zero => A.unit, Succ(m) => MonoidRel::range(op, m, f) ∙ f(m) }
}
```

Sums over `Fin(n)`, over a list (`MonoidRel::fold` of a `map`), over the
rectangle `m × n`, over the triangle `i ≤ n` and over the antidiagonal
`i + j = n` are each defined as range sums or folds, never as a separate
recursion. Then every law about a domain is a reindexing lemma about range
sums. Finite sets come through their enumerations, and
`issues/finite-set-enumeration-and-folds.md` owns the duplicate-insensitive
fold. This layer assumes only that an enumeration is a list.

**Laws**, at `MonoidRel` or at `MonoidRel + Commutative` modulo `≈`. Each is
one theorem that serves `∑` and `∏` alike:

- **Congruence.** Pointwise `≈` gives `≈` sums. This is what lets every
  later rewrite happen inside a sum.
- **Split and shift.** `∑_{k<m+n} f = ∑_{k<m} f ∙ ∑_{k<n} f(m+k)`, the
  empty sum, and the singleton.
- **Reverse** (`k ↦ n-1-k`) and **permutation invariance** for a bijection
  of `Fin(n)`. These need commutativity.
- **Exchange.** Rectangle Fubini, and the triangle-to-antidiagonal reindex
  `∑_{n<N} ∑_{i+j=n} = ∑_{i+j<N}`. The second is the one that makes Cauchy
  products, convolution associativity and power-series composition work.
- **Distributivity** at a semiring: `c * ∑ f ≈ ∑ c * f`, and the product of
  two sums as a rectangle sum.
- **Order**, at `OrderedAddGroup`: monotonicity, nonnegativity, and the
  triangle inequality `|∑ f| <= ∑ |f|`. Every tail estimate needs these.

**Surface.** The big-operator binder production `∑ k < n, f(k)` belongs to
`issues/notation-extensibility.md` and is not implemented. The library does
not wait for it. It is spelled `MonoidRel::range(+, n, λ k => f(k))` or, at
a carrier with a designated `+`, a short wrapper such as `Rat::sum(n, f)`.
When the production lands, it elaborates to the same terms.

**Tactics.** `ring` does not see through `∑`. Most sum manipulations here
are reindexings, which are better as named lemmas than as a normaliser. A
`sum_simp` (split off the last term, pull out constants) is a later
convenience and is not scheduled.

### Layer A′: difference calculus

The finite analogue of calculus is exact, and it is the earliest place
where "start intricate" pays off. With `Δf(k) = f(k+1) - f(k)`, at a
commutative ring (no division):

- **The fundamental theorem.** `∑_{k<n} Δf(k) ≈ f(n) - f(0)`, which is
  telescoping. Its order form (`Δf <= g` gives `f(n) - f(0) <= ∑ g`) is the
  discrete mean value inequality that §6 lifts.
- **Summation by parts** (Abel): `∑ f·Δg = [f g] - ∑ Δf · g(·+1)`.
- **Falling factorials** `x^{\underline m}` are the monomials of Δ:
  `Δ x^{\underline m} = m · x^{\underline{m-1}}`. So `∑_{k<n}
  k^{\underline m} · (m+1) ≈ n^{\underline{m+1}}`, and power sums follow
  through Stirling numbers.
- **Geometric sum**, multiplied out: `(1 - r) · ∑_{k<n} r^k ≈ 1 - r^n`. It
  needs no apartness, and `Series::decay` becomes an instance.
- **The binomial theorem** at a commutative semiring:
  `(a + b)^n ≈ ∑_{k≤n} C(n,k)·a^k·b^{n-k}`, with `C(n,k)` cast through the
  semiring's `of_nat`. Vandermonde's identity comes by the same route.
- **Newton's forward-difference formula** `f(n) = ∑_{k≤n} C(n,k)·Δ^k f(0)`.
  This is the discrete Taylor theorem. It is exact, it has no remainder, and
  it is a finite-sum identity. The continuous Taylor theorem is its scaling
  limit, and that is the right way round to think about it.

## 4. Layer B: truncated and formal power series

A formal power series over a commutative ring `A` is a coefficient
function, with `≈` taken coefficientwise:

```heather
// Sketch.
record PowerSeries<A> { coeff: Nat → A }
fn PowerSeries::Same(f, g) → Type { (n: Nat) → f.coeff(n) ≈ g.coeff(n) }
fn PowerSeries::mul(f, g) → PowerSeries<A> { PowerSeries(λ n => ∑_{(i,j) ∈ antidiag(n)} f.coeff(i) * g.coeff(j)) }
```

- **Ring.** Addition is pointwise, and the product is Cauchy convolution,
  which is a Layer A sum over the antidiagonal. Associativity of the
  product is the triangle exchange of §3, which makes this the first serious
  customer of Layer A. The instance is `CommRingOfInt` at the series' `≈`,
  so `ring` works on series by #219's route.
- **Polynomials** are series with a degree bound (`∃ d, ∀ n ≥ d, coeff(n) ≈
  0`, with `d` as data). Jets `Jet(A, N)` are series modulo `x^{N+1}`, that
  is, `≈` on the coefficients below `N+1` only. That quotient is a ring, and
  truncation is a ring homomorphism. All three compute at `Rat`, and a
  coefficient is a finite computation.
- **The formal derivative** `D` is a derivation (`D(fg) ≈ Df·g + f·Dg`, by
  reindexing). **Composition** `f ∘ g` is defined when `g.coeff(0) ≈ 0`.
  Only coefficients up to degree `n` of `f` contribute to coefficient `n` of
  the composite, so each one is a finite sum. That finiteness property is
  exactly what transseries generalise (§10).
- **exp and log** over a `ℚ`-algebra, which needs `1/n!`: an `OrderedField`
  or a small `RatAlgebra` class with `of_rat`. Formal `exp(a+b) ≈
  exp(a)·exp(b)` (in `A[[x, y]]`, or at `a = c·x`, `b = d·x` in `A[[x]]`)
  is the binomial theorem coefficientwise. `D(exp) ≈ exp`, and `D f ≈ 0`
  implies `f ≈ const`, because `(n+1)·a_{n+1} ≈ 0` gives `a_{n+1} ≈ 0` once
  `n+1` is invertible. Formal `sin² + cos² ≈ 1` follows: the derivative of
  the left side is `0` and its constant term is `1`.
- **Newton iteration** in `A[[x]]` doubles the number of correct
  coefficients per step. It handles inverses (when `coeff(0)` is a unit),
  square roots, and roots of a polynomial equation whose derivative is
  invertible at `x = 0` (Hensel). It is purely algebraic, and §9 needs it.
- **Jets and automatic differentiation.** `Jet(A, 1)` is the dual numbers.
  Evaluating a polynomial program at `x + ε` gives `f(x) + f'(x)·ε`, where
  `f'` is the formal derivative. That theorem is forward-mode AD, and the
  transpose is reverse mode. `issues/ml-layers-reverse-mode.md` asks for "the
  formal derivative on polynomial layers", and this layer is that.
  `Jet(A, N)` is Taylor-mode AD.

This layer is also the algebraic content of synthetic differential
geometry, without its axiom. SDG's Kock–Lawvere axiom says every map on the
nilpotent infinitesimals `D = {ε | ε² = 0}` is affine, which contradicts
excluded middle. Here, `ε` lives in a quotient ring (the jets), so no axiom
is needed. For polynomial maps the affine property is a theorem of this
layer. For general maps it holds up to `o(h)`, and that is the definition
of differentiability in §6.

Multivariate series (`A[[x, y]]` as `Nat × Nat → A`, or iterated) are
deferred until a customer needs more than the two-variable `exp` law.

## 5. Layer C: approaches and quantitative asymptotics

### 5.1 Not filters

Mathlib founds limits and Landau notation on filters. A filter on `A` is a
predicate on predicates, `(A → Type) → Type`, and analysis is
`Tendsto f l₁ l₂` together with `IsBigO l f g`. That works in a classical,
impredicative `Prop`. For Heather it has three costs:

- In a predicative kernel a filter lives one universe above its carrier.
  A function from filters to filters raises the universe again.
- A filter's membership proofs carry no computational content that a
  client can use. A threshold is hidden inside the proof that a set is in
  the filter.
- Much of the filter API (`Eventually` and `Frequently` as duals,
  ultrafilters, `limsup`) leans on double negation.

What analysis on `ℝ` and on sequences uses in practice is a filter
**basis**, indexed by something small. That means thresholds `N` for `n →
∞`, and radii `1/(k+1)` for `y → x`. Both bases are countable and nested.
So that is the structure to take.

### 5.2 Approaches

```heather
// Sketch. A decreasing sequence of neighbourhoods.
record Approach<A> {
    near: Nat → A → Type,
    mono: (k: Nat, y: A) → near(Succ(k), y) → near(k, y),
}

fn Approach::Eventually<A>(self l: Approach<A>, P: A → Type) → Type {
    ∃ k: Nat, (y: A) → l.near(k, y) → P(y)
}
```

The instances are:

- `n → ∞` on `Nat`, with `near(k, n) := k <= n`.
- `y → x` on `CReal`, with `near(k, y) := |y - x| <= 1/(k+1)`.
- `y → x` within a set `S`, with the conjunction.
- `y → x⁺`, with an added `x < y`. This needs `<` as data, which is
  constructive.
- `y → ∞` on `CReal`, with `near(k, y) := k <= y`.
- `ε → 0⁺` for perturbation parameters.

Nets and general directed bases are out of scope. The reals are first
countable, constructively too, and every approach in sight is countable. If
a customer ever needs uncountable bases (germs at a point of a function
space, say), `Index` becomes a field with a directedness law, and this
record is the instance at `Nat`.

`CReal::Same(x, y)` is then literally `(k) → (n → ∞).Eventually(λ n => |x_n
- y_n| <= 1/(k+1))`. The first round should restate it that way (as a
theorem relating the two, not by changing the definition) to prove the
layer fits.

### 5.3 Landau relations with their witnesses

At an approach `l` on `A` and functions into an ordered field `F` with
`abs` (`Rat`, `CReal`):

```heather
// Sketch. Constants are rationals so they compare by evaluation.
fn BigO(l, f, g) → Type { ∃ C: Rat, l.Eventually(λ y => |f(y)| <= ofRat(C) * |g(y)|) }
fn LittleO(l, f, g) → Type { (k: Nat) → l.Eventually(λ y => |f(y)| <= ofRat(inv_succ(k)) * |g(y)|) }
fn Asym(l, f, g) → Type { LittleO(l, λ y => f(y) - g(y), g) }          // f ~ g
fn Tendsto(l, f, L) → Type { LittleO(l, λ y => f(y) - L, λ _ => 1) }
```

- **The data is the point.** A `LittleO` proof is a modulus `Nat → Nat`,
  the threshold for each `1/(k+1)`. This is the shape of `CReal`'s
  regularity, of Bishop's `δ(ε)`, and of proof mining's rates of
  convergence. A limit computed from it computes.
- **No division.** `~` is `f - g = o(g)`, never `f/g → 1`, because `g` may
  vanish and apartness from zero would have to be threaded through.
- **The algebra, proved once**: `O` and `o` are closed under `+` and scalar
  multiples; `O(f)·O(g) ⊆ O(fg)` and `o(f)·O(g) ⊆ o(fg)`; transitivity,
  `o ⊆ O`, and `~` is an equivalence. Composition is the remaining law: a
  map `φ` from approach `l₁` to `l₂` "tends" when a modulus `m` sends
  `near₁(m(k))` into `near₂(k)`, and then `f = o(g)` at `l₂` gives `f ∘ φ =
  o(g ∘ φ)` at `l₁`. Continuity, limits of compositions and the chain rule
  all use this one lemma.
- **Scales.** An asymptotic scale is a sequence `φ_0, φ_1, …` with
  `φ_{k+1} = o(φ_k)`. Examples are `x^k` at `x → 0`, `n^{-k}` at `n → ∞`,
  and `x^a log^b x` ordered lexicographically.
- **Tactic.** `asymp` would normalise `O`-terms the way computer algebra
  truncates series. Its certificate is a chain of closure lemmas, which is
  the same shape as `by intervals()`. It is later, and filed with Layer D.

The first customer needs no real functions at all: sequences `Nat → Rat` at
`n → ∞`. That covers `Series::fine`, the regularity bounds, and statements
like `cost(n) = O(n log n)` about compiled programs, should
`heather-in-heather` want to state complexity rather than measure it.

## 6. Layer D: certified expansions and the derivative

### 6.1 The record

```heather
// Sketch. A finite part in a scale and a remainder at the scale's next step.
record Expansion<A>(l: Approach<A>, scale: Nat → A → F, f: A → F, N: Nat) {
    coeff: Nat → F,                     // only the first N matter
    C: Rat, at: Nat,                    // the remainder's constant and neighbourhood
    rem: (y: A) → l.near(at, y) → |f(y) - ∑_{k<N} coeff(k) * scale(k, y)| <= ofRat(C) * |scale(N, y)|,
}
```

The remainder has two readings, and constructively they are one:

- **Uniform**, on the neighbourhood `near(at)`. With a polynomial scale on
  an interval domain this is a **Taylor model** (Berz and Makino), which is
  a polynomial plus an interval remainder. An `Interval` is the order-0
  Taylor model. Taylor models beat interval arithmetic on the dependency
  problem: `x - x` cancels symbolically and does not widen. That makes them
  the natural growth path for `by intervals()` once enclosures need to be
  tight over a range, not only at a point.
- **Asymptotic**: `f - ∑ = O(φ_N)` at `l`. This is a Poincaré expansion.
  Because `O`'s threshold and constant are data (§5.3), the asymptotic
  reading is the uniform one with the neighbourhood forgotten. One record
  serves both, and the asymptotic statement is a projection of it.

Operations on expansions (sum, product truncated at `N`, composition,
reciprocal when the leading coefficient is apart from zero) each come as a
pair: the coefficient computation, which is the jet algebra of Layer B, and
a remainder lemma, which is the closure algebra of Layer C. **The map from
an expansion to its jet is a ring homomorphism into `Jet(F, N)`, and it
sends composition to jet composition.** Each rule is a ring identity in
`Jet` plus a bound, proved once and at every order.

### 6.2 The derivative

`f` is **uniformly differentiable on `S` with derivative `g`** when one
modulus serves every point: for each `k` there is a `δ` such that `x, y ∈
S` and `|y - x| <= δ` give `|f(y) - f(x) - g(x)(y - x)| <= (1/(k+1))·|y -
x|`. That is Bishop's definition, and it is a uniform first-order expansion
of `f(x + h)` in the scale `1, h`, with the remainder `o(h)` and its modulus
independent of `x`. Order-`N` differentiability is the order-`N` expansion,
with the jet as its coefficients.

This settles the design question in `issues/real-functions-and-derivatives.md`.
Use Bishop's uniform derivative on a set (an interval first), stated as a
uniform expansion, and let it inherit everything above:

- The **rules** (sum, product, chain, quotient where the denominator is
  apart from zero, and Faà di Bruno at order `N`) come from §6.1.
- The **derivative is unique** on a set with no isolated points, which
  needs points apart from `x` arbitrarily close by.
- The **mean value inequality**: `|g| <= M` on `[a, b]` gives `|f(b) -
  f(a)| <= M·|b - a|`. The proof cuts `[a, b]` into `n` pieces, applies the
  uniform expansion on each piece, and telescopes, which is Layer A′'s
  discrete mean value inequality. Constructively this is the right form,
  where Rolle's theorem is not. From it, `g ≈ 0` gives `f` constant.
- **Taylor's theorem** with remainder is the statement that `N` successive
  uniform derivatives give an order-`N` uniform expansion whose jet is
  `f^{(k)}/k!`. It becomes a theorem about this record, not a foundation.

A pointwise (non-uniform) derivative is weaker and constructively
ill-behaved: it does not give a mean value inequality without uniformity.
It can be defined at a point as a non-uniform expansion if a customer needs
it, but it is not the default.

## 7. Layer E: series and analytic functions

- **A series** is the range sum of its terms (Layer A) with a tail modulus.
  Convergence is `Tendsto` at `n → ∞` (Layer C), and the limit is a
  `CReal` through `CReal::lim`. Comparison against a majorant, with explicit
  rates, is the one test the library needs first.
- **Rebasing `Series`.** `Series::sum` becomes the range sum, and
  `Series::tail` and `Series::decay` become the telescoping and geometric
  lemmas of Layer A′ applied to the ratio bound. The ratio record stays as
  it is: it is the fast enclosure route (a majorant at ratio `1/2`), and
  `by intervals()` depends on its shape. Rebasing is a refactor that
  changes no statement `elementary.hthr` exports.
- **Power series with a radius.** A `PowerSeries<Rat>` with a Cauchy
  majorant `|a_n| <= M / r^n` (with `M` and `r` rational, as data) is an
  analytic function on `|x| < r`. Evaluation at a `CReal` `x` with `|x| <=
  r' < r` converges at a geometric rate fixed by `r'/r`. **The evaluation
  map is a ring homomorphism on the disc**: sums are immediate, and products
  are the Cauchy product theorem. Majorants multiply, and the product of
  two geometric tails is bounded through the triangle sums of §3.
- **The laws of the elementary functions** then need no derivatives of real
  functions. Each formal law of §4 (`exp(a + b)`, `sin² + cos²`, the
  addition formulas) maps through the evaluation homomorphism to a law at
  `CReal`. For `elementary-functions-at-reals`, this is the "Cauchy product"
  route, made generic so that it is proved once for every identity rather
  than once per identity. Real arguments come for free, because evaluation
  is defined at any `CReal` in the disc. Monotonicity of `exp` comes from
  `exp(x) = exp(x/2)²` and `exp(h) >= 1 + h` for `h >= 0`. It does not need
  the mean value theorem.
- **Uniqueness by an equation.** `exp` as the unique solution of `f' = f`,
  `f(0) = 1`, needs §6. It is a second characterisation, proved after the
  first, not the definition.

Generic coefficient carriers (complex numbers for `e^{ix}`, matrices for
`exp(A)`, jets for `exp(x + ε)`) want a complete normed commutative ring.
That class is deferred until a customer needs one: the first carrier is
`Rat` coefficients evaluated at `CReal`. `exp` on `Jet(F, N)` needs nothing
analytic at all, because `ε` is nilpotent: `exp(x + ε) = exp(x)·∑_{k≤N}
ε^k/k!`. That is how `exp' = exp` appears on the jet side.

## 8. The showcase: Euler–Maclaurin, harmonic numbers, Stirling

The result that shows why Taylor series should not be the core is an
expansion that diverges. Stirling's

    log n! = n log n - n + ½ log n + log √(2π) + ∑_{j≥1} B_{2j} / (2j(2j-1) n^{2j-1})

has a series that converges for no `n`, yet every truncation is an
excellent approximation. It is meaningful only as a Poincaré expansion at
`n → ∞` in the scale `n^{-k}`, which is Layer D. A library founded on
convergent Taylor series cannot even state it.

The first target is the easier relative, `H_n = log n + γ + 1/(2n) + O(1/n²)`.
It needs:

- `log` (`issues/interval-log-and-reduction.md`).
- The expansion of `log(1 + 1/k)` at `k → ∞` (Layer D, from the power
  series of `log(1+x)` composed with `1/k`).
- Summing the expansions, which is Layer A′. This avoids integrals:
  `∑ (1/k - log(1 + 1/k))` converges with an explicit tail, which defines
  `γ`.

Stirling then needs the Bernoulli numbers, which are the coefficients of
the formal series `x/(e^x - 1)` (a Layer B reciprocal). It also needs the
Euler–Maclaurin remainder in its summation-by-parts form. Wick's
`Numerics/Asymptotics` (Gevrey series, Borel summation;
`docs/wick-survey.md`) is the longer road from here.

## 9. Layer F: perturbation theory

**Regular perturbation.** Take an equation `F(x, ε) = 0` with `F(x₀, 0) =
0` and `∂F/∂x` invertible at `(x₀, 0)`. The formal solution `x(ε) ∈
A[[ε]]` comes from Newton lifting (Layer B). Each coefficient solves a
linear equation with the same invertible derivative, so it computes at
`Rat`. The analytic statement is the order-`N` expansion of the true
solution (Layer D) with remainder `O(ε^{N+1})`. Its proof is a contraction
with an explicit rate. Banach's fixed-point theorem is constructive with
rates, and the rate gives the remainder's constant. The first instances are
roots of a polynomial with perturbed coefficients, then fixed points of a
parametrised contraction. Eigenvalue perturbation waits for
`finite-linear-algebra`, and ODEs in a parameter wait for Picard iteration.

**Float error analysis is first-order perturbation in `u`.** The standard
model `fl(x ∘ y) = (x ∘ y)(1 + δ)` with `|δ| <= u`, and `Format::gamma_add`
(`γ_m + γ_n + γ_m γ_n <= γ_{m+n}`), is `O`-arithmetic with explicit
constants at the approach `u → 0⁺`. Nothing in `lib/std/num/float/` needs
restating. The asymptotic layer should be able to read "error `= n·u +
O(u²)`" as a projection of the existing `γ_n` bounds, which is a good
probe that Layer D's records fit a mature existing customer.

**Singular perturbation** needs two things that are not power series: the
fractional powers `ε^{1/q}` of Puiseux series, where the monomial monoid
becomes `ℚ`, and exponentially small terms `e^{-1/ε}`. Both enter the
monomial group of §10, which is where transseries come in. Matched
asymptotics and WKB are out of scope.

## 10. Layer G: transseries (horizon)

A transseries is a generalised power series `∑ c_𝔪 𝔪` over a totally
ordered monomial group `𝔐` built from `x`, `exp` and `log` (`x^a`, `e^x`,
`e^{x log x}`, `log log x`, …), whose support is small enough that products
are defined. The transseries form an ordered differential field closed
under composition. Aschenbrenner, van den Dries and van der Hoeven show
that its theory as an ordered differential field is model complete and
explicitly axiomatised, and so decidable, which makes it a complete theory
of "asymptotic analysis" in a precise sense. It is the natural end point of Layers B–D, where every
reasonable germ has an expansion and the expansions form a field.

Design consequences for Heather:

- **Grid-based, not well-based, supports.** Well-based supports (Hahn
  series: no infinite ascending chain in the dominance order) need
  well-orders, which are constructively delicate. Grid-based supports (van
  der Hoeven) are contained in `𝔪 · 𝔫₁^ℕ ⋯ 𝔫_k^ℕ` for finitely many
  infinitesimal monomials. They are finite descriptions, and each
  coefficient of a product is a finite sum. That is the same finiteness
  that makes power-series composition work (§4), so this is the
  computational choice.
- **The leading term is data.** The order on transseries is the sign of
  the leading coefficient, which needs to know which coefficients vanish.
  That is undecidable for an infinite coefficient stream, even over `Rat`,
  and for `CReal` coefficients it is undecidable outright. So positivity has
  to be witnessed: an index (monomial) below which coefficients are `≈ 0`
  and at which the coefficient is positive. This is exactly how `CReal`
  positivity is witnessed, by an index with a rational gap. The constructive
  pattern is the one the reals already use, apartness with data, one level
  up.
- **Build the tower in steps.** The steps are Laurent series (`𝔐 = ℤ`,
  which is already an ordered field with witnessed leading terms), then
  Puiseux (`ℚ`), then `x^a log^b x`, then exponentials, which is the step
  where closure needs the transfinite tower. Each step is a useful object
  on its own, and the first two serve singular perturbation (§9).
- **The hook to leave now.** Write Layer B's convolution as a sum over a
  named `antidiag(n)`, the list of factorisations of `n` in the monomial
  monoid. Transseries replace `Nat` and `antidiag` with a grid and its
  finite factorisation lists. Layer B should not be made generic over the
  monoid in its first round, which would cost every client for a customer
  years out, but the name keeps the substitution mechanical.

The customers are Wick's asymptotics research, asymptotics of recurrences
(divide-and-conquer costs), and the ADH theory itself as a long-term
mathematics showcase. This is research, filed so that the earlier layers
are shaped by it, not scheduled.

## 11. Integration, briefly

Integration is not one of these layers, but they decide its first form. A
uniformly continuous function on `[a, b]` (with its modulus as data) has a
Riemann integral as the limit of range sums over uniform partitions. The
tail modulus comes from the continuity modulus, and the limit is a
`CReal::lim`. That is Bishop's integral. It is Layer A plus Layer C, and it
gives the fundamental theorem of calculus against §6's derivative by
telescoping (Layer A′ again). Measure-theoretic integration, and the
counting-measure view of `∑`, stay with `big-operator-semantics` and the
measure work (roadmap mathematics item 4). This route does not compete
with them: Riemann sums are simple-function integrals.

## 12. Order of work

Each step names what it unblocks. The slugs are the issues filed with this
note.

| # | Issue | Layer | Needs | Unblocks |
|---|---|---|---|---|
| 1 | `finite-sums-and-products` | A | semiring layers (done) | everything below, plus `finite-linear-algebra`'s `Fin n` sums |
| 2 | `finite-difference-calculus` | A′ | 1 | binomial theorem (4, 6), geometric tails (6), mean value inequality (5) |
| 3 | `asymptotic-relations` | C | `CReal` (done), 1 | limits, continuity, `math-reals`' "sequences, limits, continuity" |
| 4 | `formal-power-series` | B | 1, 2, `ring` at `≈` (#219) | formal laws of `exp`/`sin`/`cos`, the formal derivative for `ml-layers`, Newton lifting |
| 5 | `certified-expansions` | D | 3, 4 | the derivative (`real-functions-and-derivatives`), Taylor's theorem, `asymp` |
| 6 | `power-series-evaluation` | E | 2, 3, 4 | `elementary-functions-at-reals`' laws, real arguments, rebasing `Series` |
| 7 | `taylor-model-enclosures` | D (uniform) | 5, intervals (#208) | tighter `by intervals()` over ranges, `float-transcendental` specs |
| 8 | `harmonic-and-stirling-asymptotics` | showcase | 5, 6, `log` | the first divergent expansion, and γ |
| 9 | `regular-perturbation-expansions` | F | 4, 5, contraction with rates | perturbed roots, fixed points, the float error reading |
| 10 | `grid-based-transseries` | G | 4, 5, 9 | research horizon |

Items 1–3 can run in parallel once 1's range sum exists. Item 3 does not
need 2, and 4 needs only 1's exchange lemmas and 2's binomial theorem. Item
4 is the one with an outside customer waiting (`ml-layers`). Items 5 and 6
are what `math-reals` is waiting on in substance.

**On the roadmap.** `docs/roadmap.md` puts "asymptotics and transseries" at
item (5) of the mathematics order, after measure. This note argues that the
foundational part of asymptotics (items 3 and 5 above) is what item (2)'s
`math-reals` milestone ("sequences, limits, continuity") consists of. On
that reading it moves up beside the reals, and only transseries (item 10)
stays at (5). That is a ranking change, which is Minus's call, so the
roadmap's order is not edited here.

## 13. Decisions this note makes, and the ones it leaves

Made here (each is revisable when a customer pushes back):

- **Countable nested approaches**, not filters or directed bases (§5.1–5.2).
- **Landau constants as `Rat`** and moduli as `Nat → Nat`, so bounds
  compare by evaluation (§5.3). A `CReal` constant can always be bounded by
  a rational one first.
- **No division in asymptotic definitions**: `~` is `f - g = o(g)`.
- **Bishop's uniform derivative on a set** as the default, stated as a
  uniform expansion (§6.2).
- **Formal identities first, then the evaluation homomorphism** as the
  route to the laws of the elementary functions (§7).
- **Grid-based supports** for any transseries (§10).

Left open:

- The roadmap move in §12.
- Whether `PowerSeries` over several variables is an iterated series or a
  multi-index function. Decide at the first two-variable customer.
- The normed-ring class for generic series carriers (§7). Decide at the
  first non-`Rat` coefficient customer (complex `exp`, or matrix `exp` for
  linear ODEs).
- The concrete surface spelling of `∑` before the binder production lands.

## 14. Non-goals

- No change to `CReal`'s representation, to `Series`'s exported statements,
  or to the kernel.
- No new notation production. `∑ k < n, f(k)` waits for
  `notation-extensibility`.
- No filters, no ultrafilters, no nonstandard analysis, and no SDG axiom.
  §4 explains what is kept from SDG without the axiom.
- No measure theory here. §11 states only the integral that falls out.

## References

- E. Bishop and D. Bridges, *Constructive Analysis* (1985), ch. 2 (uniform
  derivative, integral) and ch. 5 (moduli).
- J. Dieudonné, *Calcul infinitésimal* (1968): développements limités and
  the asymptotic scales of §5.3.
- R. Graham, D. Knuth and O. Patashnik, *Concrete Mathematics*, ch. 2 and 9
  (finite calculus; asymptotics with `O`).
- N. G. de Bruijn, *Asymptotic Methods in Analysis*: Euler–Maclaurin,
  Stirling.
- K. Makino and M. Berz, "Taylor models and other validated functional
  inclusion methods" (2003).
- J. van der Hoeven, *Transseries and Real Differential Algebra*, LNM 1888
  (2006): grid-based transseries.
- M. Aschenbrenner, L. van den Dries and J. van der Hoeven, *Asymptotic
  Differential Algebra and Model Theory of Transseries* (2017).
- U. Kohlenbach, *Applied Proof Theory* (2008): moduli and rates as the
  computational content of analytic statements.
- A. Kock, *Synthetic Differential Geometry* (2nd ed. 2006): the axiom §4
  does without.
