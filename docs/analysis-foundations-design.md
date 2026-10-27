# Foundations for analysis: two structures and where they meet

Status: design and survey, 2026-10-27, revised the same day after Minus's
review. No code lands with this note. The rounds it orders are filed as
issues (§13).

It answers part of `issues/big-operator-semantics.md` (the finite case,
§4). It answers the design question in
`issues/real-functions-and-derivatives.md` (which derivative, §3.1 and
§7). It proposes a route to the laws in
`issues/elementary-functions-at-reals.md` (§8).

## 1. The thesis

The usual road through analysis treats Taylor series as the thing the
library is for. Limits come first, then derivatives, then iterated
derivatives, then Taylor's theorem, and then `exp`, `sin` and `cos` defined
as their series, with every later result going back through that chain.
Heather's current `exp`/`sin`/`cos` (`lib/std/num/float/elementary.hthr`)
already follow it. They are series with a ratio bound, and their laws are
stuck because each law needs analysis that does not exist yet.

The goal is a foundation general enough to reach a list of very different
places with no change of footing:

- perturbation theory, regular and singular;
- transseries;
- machine-learning theory (backprop, width expansions);
- more exotic spaces (manifolds, `p`-adics).

The proposal is that analysis rests on **two orthogonal structures and the
place where they meet**. Taylor series is the most degenerate instance of
both.

- **A differential structure** (§3.1) says what a derivative is, without
  saying what the spaces are: a derivative that is linear in the direction,
  satisfies the chain rule, and has a reverse form. Cartesian differential
  categories, reverse derivative categories and tangent categories
  axiomatise it. Its instances include:
  - jets and polynomials;
  - coefficient streams;
  - functions on `CReal` with a uniform or interval derivative;
  - programs;
  - parametrised models in ML;
  - manifolds.
- **A dominance relation** (§3.2) says what "small" is and how expansions
  converge: `f ≼ g`, meaning "`f` is `O(g)`", as a relation with axioms,
  together with completeness and **Newton's lemma**. Its instances include:
  - `ε`-adic power series, which is regular perturbation;
  - Puiseux series, which is singular perturbation;
  - transseries;
  - `p`-adic numbers;
  - germs at an approach, which is ordinary asymptotics;
  - `1/width` expansions.
- **Where they meet** (§3.3): differential-valued fields, in which the
  derivative respects the dominance relation. This is the theory that
  transseries and Hardy fields live in, and it is the long-term target.

Two choices cut across both structures:

- **Representation by calculus in coinductive form** (§3.4). An expansion
  is its stream of derivatives at a point, differentiation is `tail`, a
  function is defined by the differential equation it satisfies, and laws
  are proved by bisimulation.
- **Automation by decision procedures that emit certificates** (§3.5). WZ
  pairs handle sums, holonomic closure handles functions defined by linear
  ODEs, and Gruntz's algorithm handles limits of exp-log expressions. Each
  is checked the way `omega` and `ring` are.

The concrete layers that the first draft of this note proposed are kept as
the **first instances** of the core (§4–§12). They are:

- finite sums and difference calculus;
- Hurwitz series and jets;
- witnessed asymptotics;
- certified expansions;
- series evaluation.

They are what to build first. Each interface is filed early and validated
by two of them (§3.7).

| Result | How it falls out |
|---|---|
| Derivative | a map paired with derivative evidence (§3.1). On `CReal` the evidence is a uniform first-order expansion, which is Bishop's derivative (§7) |
| Sum, product, chain rules, Faà di Bruno | closure of the differential structure. For each instance, ring identities on jets plus one remainder lemma per operation |
| Taylor's theorem | relates order-`N` expansions to iterated derivatives. It is a theorem and defines nothing |
| `exp`, `sin`, `cos` | defined by `exp' = exp` and `sin' = cos`, `cos' = -sin` over any commutative ring (§5) |
| `sin² + cos² = 1`, `exp(a+b) = exp(a)·exp(b)` | the derivative is zero and the heads agree, so they are equal by coinduction (§3.4), and evaluation carries them to `CReal` (§8) |
| Limits, continuity | `f - L ≺ 1` at an approach (§6) |
| Regular perturbation | Hensel lifting in the `ε`-adic dominance (§3.2, §10) |
| Singular perturbation | the Newton polygon (tropical geometry), giving Puiseux exponents (§10) |
| Stirling, harmonic numbers | divergent asymptotic expansions at `n → ∞` (§9), which a Taylor-first library cannot state |
| Float error analysis | first-order perturbation in `u`. `Format::gamma_add` is already `O`-arithmetic (§10) |
| Backprop, optimisers | a reverse differential structure on parametrised maps (§3.1) |
| Width expansions (PDLT) | perturbation in `1/n` at `n → ∞` (§10) |
| Transseries | the meeting point (§3.3) with log-exp monomials (§11) |
| Sum identities, ODE identities, limits | WZ certificates, holonomic closure, Gruntz (§3.5) |

None of this is new mathematics. What is particular to Heather is that, in
a constructive kernel, the witnesses are data:

- a derivative is carried, never asserted to exist;
- a leading monomial is carried, never computed by a zero test;
- a remainder's constant and threshold are values.

Carrying the witnesses is what lets "asymptotic" and "validated" be one
record (§7), and it is the same pattern `CReal` already uses for
positivity.

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
   §4. `Series::tail` is a telescoping identity fused with a geometric
   majorant estimate.
2. **"Eventually, with the threshold as data" is already written three
   times.** `CReal::Same` is `(k) → ∃ start, (n) → start <= n → |x_n - y_n|
   <= 1/(k+1)`. `regular` is the same bound in uniform form, and `Series`
   has its `start`. Each copy has its own index arithmetic. This is the
   asymptotic layer of §6, unnamed.
3. **The laws of `exp` are blocked on a finite identity.** The `n`-th term
   of the Cauchy product of the `exp` series at `a` and `b` is
   `∑_{i+j=n} a^i/i! · b^j/j! = (a+b)^n/n!`, which is the binomial theorem.
   The only analysis left after that is the tail of a product of two
   geometrically dominated series. In the Hurwitz convention of §5 even
   the binomial step disappears: both sides solve `F' = (a+b)·F`.
4. **Float error analysis already does `O`-arithmetic.** `gamma_add` is the
   statement that `(1+θ_m)(1+θ_n) = 1+θ_{m+n}`, with second-order terms
   absorbed. It is perturbation theory in `u` to first order, with explicit
   constants.

## 3. The general core

### 3.1 Axis 1: differential structure

The most general notion of derivative that still has a chain rule comes
from three axiomatisations:

- **Cartesian differential categories** (Blute, Cockett and Seely, 2009).
  The maps go between objects that carry commutative-monoid structure. Each
  map `f: A → B` has a derivative `D[f]: A × A → B`, taking a point and a
  direction. Seven axioms govern it:
  - `D` is additive in `f`;
  - `D[f]` is linear in the direction;
  - identities and projections are their own derivatives;
  - `D` respects pairing;
  - the chain rule holds: `D[g ∘ f](x, v) = D[g](f(x), D[f](x, v))`;
  - mixed second derivatives are symmetric.
- **Reverse derivative categories** (Cockett and others, 2020). These add
  `R[f]: A × B → A`, which takes a point and a cotangent and gives a
  cotangent. They are reverse-mode AD as an axiom system. Cruttwell,
  Gavranović, Ghani, Wilson and Zanasi (2022) build gradient-based learning
  on them: models are parametrised maps, learners are lenses, and
  optimisers are lens morphisms.
- **Tangent categories** (Rosický, 1984; Cockett and Cruttwell, 2014). These
  drop the Cartesian assumption and use a tangent-bundle functor `T`
  instead, for spaces that are not vector spaces. That covers manifolds,
  diffeological spaces, models of synthetic differential geometry, and the
  algebraic case of Kähler differentials.

A **derivation** `∂` on a commutative ring is the one-object algebraic
shadow of this. The Leibniz rule is the chain rule applied to
multiplication. A derivation is all that transseries need (§3.3).

**How Heather carries it.** A differentiable map is a map paired with its
derivative and the evidence that links them. The derivative is never
asserted to exist. This is how AD works in practice: dual numbers carry
`(f(x), f'(x))`. It is also the constructive reading of Bishop's derivative.

```heather
// Sketch. The evidence predicate is what an instance supplies.
record Diff<A, B> { map: A → B, deriv: A → A → B, ok: Deriv(map, deriv) }
// id, compose (chain rule), pair, sum: closure theorems per instance,
// stated once as the interface's laws.
```

A **smooth** map is a map whose derivative is again differentiable, without
end. That makes smoothness coinductive: the `C^∞` evidence is a stream of
derivative evidence, and `C^k` is `k` unrollings. This is the same
structure as §3.4, one level up.

| Instance | Derivative evidence | Laws proved by |
|---|---|---|
| polynomials and jets over a ring | formal derivative, exact | `ring` |
| Hurwitz series (§5) | the shift | coinduction (induction on the index) |
| `C¹` functions on `CReal` (§7) | a uniform first-order expansion with its modulus | the asymptotic closure lemmas (§6) |
| Lipschitz functions on `CReal` | an interval enclosure of slopes (Edalat and Lieutier) | enclosure. The chain rule holds as an inclusion, so this is a *lax* instance |
| programs | a source transformation | proved once (`ml-layers`, `hih-passes`) |
| ML models | a reverse structure on parametrised maps | the reverse axioms |
| manifolds and the like | a tangent structure | later |

The Edalat–Lieutier derivative earns its place. It is defined for every
Lipschitz function, at a kink like ReLU's it is Clarke's generalised
gradient, and the fundamental theorem of calculus holds for it. Wick's
practical backward pass with subgradients is exactly this instance, and its
enclosures are the interval arithmetic Heather already has.

### 3.2 Axis 2: dominance, convergence, Newton

A **valuation** on a ring `A` is a map `v: A → Γ ∪ {∞}` into an ordered
group of monomials, with `v(ab) = v(a) + v(b)` and `v(a + b) ≥ min`.
Computing `v` means finding the first nonzero coefficient, which is
undecidable for an infinite expansion even over `Rat`. So Heather does not
take `v` as primitive. It takes the relation that a valuation induces,
which Aschenbrenner, van den Dries and van der Hoeven also work with
directly:

- a **dominance relation** `f ≼ g` ("`f` is `O(g)`"), a preorder with
  `f ≼ 0 → f ≈ 0`, `f ≼ h ∧ g ≼ h → f + g ≼ h`, and `f ≼ g → fh ≼ gh`;
- `f ≺ g` ("`f` is `o(g)`") with its witness as data;
- **no totality**, since constructively two germs need not be comparable.

A leading monomial, when one is needed (the sign of a transseries, a
reciprocal), is carried as data: an index below which the coefficients are
`≈ 0`, and a coefficient apart from zero at that index. That is how `CReal`
carries positivity, one level up.

**Landau's `O` at an approach (§6) satisfies these axioms**, so ordinary
asymptotics is the archimedean instance of this axis. The `ε`-adic order on
power series, the `p`-adic order and transseries' dominance are the
non-archimedean instances. One interface covers both.

**Convergence** is Cauchy-ness for the relation, with rates. In the
`ε`-adic case it means coefficients stabilise. On `CReal` it means
regularity.

**Newton's lemma is the central theorem.** If an approximate root `a` of
`f` has `f(a)` small against `f'(a)²`, then `a` lifts to an exact root, and
the convergence is quadratic. Non-archimedean, this is Hensel's lemma, with
the condition `v(f(a)) > 2·v(f'(a))`. Archimedean, it is Newton–Kantorovich.
Both are a contraction with a rate in a complete structure. So Heather
should prove one fixed-point theorem with rates and get both Newton lemmas
from it, rather than proving the two lemmas separately.

| Instance | Monomials | What it gives |
|---|---|---|
| germs at an approach (§6) | the functions themselves (archimedean) | limits, `O`/`o`, asymptotic expansions |
| `A[[ε]]`, the `ε`-adic order | `ε^ℕ` | regular perturbation by Hensel lifting (§10) |
| Puiseux series | `ε^ℚ` | singular perturbation. The Newton polygon is tropical geometry |
| `1/n` series at `n → ∞` | `n^{-ℕ}` | width expansions in ML theory (§10) |
| `ℚ_p` | `p^ℤ` | `p`-adic analysis, the exotic instance that comes free |
| grid-based transseries (§11) | log-exp monomials | the meeting point's main instance |

### 3.3 Where they meet: differential-valued fields

A **differential-valued field** (Rosenlicht, 1980) is a field with both a
derivation and a dominance relation. The two are compatible: roughly, a
bounded element's derivative is dominated by the logarithmic derivative of
any infinitesimal one, so small things have small derivatives on the scale
the field itself sets.

Aschenbrenner, van den Dries and van der Hoeven add an order (H-fields)
and a differential Hensel property they call **newtonian**: differential
polynomials with a suitably simple approximate zero have a true zero. This
is Newton's lemma of §3.2 lifted to differential equations, and it is what
asymptotic perturbation of ODEs is.

The instances are:

- Laurent series in `x` with `d/dx`, which compute;
- Hardy fields, meaning germs at `+∞` of real functions closed under
  differentiation;
- the transseries, which form a newtonian H-field with a model-complete,
  decidable theory.

This is Heather's long-term target for asymptotic analysis. It is stated as
a class over the two axes once both have instances (§3.7).

### 3.4 Representation: calculus in coinductive form

Pavlović and Escardó (1998) represent an analytic function at a point by
its stream of derivatives `f(0), f'(0), f''(0), …`, with no factorials.
Then:

- **Differentiation is `tail`.**
- **Bisimulation is the proof principle.** `f ≈ g` when `f(0) ≈ g(0)` and
  `f' ≈ g'`.
- **A differential equation is a definition.**
  - `exp` is the stream with head `1` and derivative `exp`.
  - `sin` and `cos` are the pair with heads `0` and `1` and `sin' = cos`,
    `cos' = -sin`.
  - `tan` has `tan' = 1 + tan²`.
  - The product is defined by the Leibniz rule: `(fg)(0) = f(0)g(0)` and
    `(fg)' = f'g + fg'`.
- **Laws are short coinductive proofs.** For `s² + c²`, the derivative is
  `2sc - 2cs ≈ 0` and the head is `1`, so it is `1`. For `exp(a + b)`, both
  sides solve `F' = F` with the same head.

Algebraically this is the ring of **Hurwitz series** (Keigher, 1997). The
product is binomial convolution, `(ab)_n = ∑_{k≤n} C(n,k)·a_k·b_{n-k}`, and
the derivative is the shift. It works over **any** commutative ring, with no
`ℚ` needed. So `exp`, `sin`, `cos` and their laws live over `ℤ`, and "the
derivative is zero, so the series is constant" holds outright, because a
zero shift means a zero tail, with no `n + 1` to invert. The bridge to
ordinary power series is `a_n ↦ a_n / n!`, and it is needed only at
evaluation (§8).

**Heather specifics.** The Leibniz product is corecursion *up to* `+`: its
tail is `f'g + fg'`, not a direct self-call. Heather's corecursion accepts a
self-call only as a direct child of the returned constructor
(`issues/codata-nested-guards.md`), and its bisimilarity is a relation,
not `=`. So the decision is to **take the method, not the datatype**:

- A series is a coefficient function `Nat → A`.
- A definition by an ODE `f' = F(f)` is course-of-values recursion, since
  coefficient `n+1` comes from coefficients `≤ n`.
- The bisimulation principle is a theorem proved by induction on `n`.

Codata becomes the better representation once corecursion up to "friendly"
operations exists (Blanchette and others, 2015). That belongs to
`codata-nested-guards`. Nothing here waits for it.

The coinductive method generalises beyond `ℕ`. Smoothness is coinductive
(§3.1). For transseries, the supports are not `ℕ`-indexed, and coinduction
over a well-based order is a research question (§11).

### 3.5 Automation: decision procedures with certificates

Each instance has decision procedures that analysts use by hand. In
Heather each one should emit a certificate that is checked as `omega` and
`ring` are checked: the search is untrusted, and the check is a
kernel-checked identity.

| Procedure | Domain | Certificate | Check |
|---|---|---|---|
| Gosper, Zeilberger, WZ pairs (*A = B*) | hypergeometric finite sums (§4): binomial identities, Vandermonde, hundreds more | a rational function `R(n, k)` | a `ring` identity after clearing denominators, then the telescoping lemma of §4 |
| holonomic closure | sequences and functions given by a linear recurrence or ODE with polynomial coefficients | the annihilating operator and initial terms | an operator identity by `ring`, then uniqueness of solutions by coinduction (§3.4) |
| Gruntz's algorithm | limits and asymptotics of exp-log expressions | the steps on the most-rapidly-varying set, with sign facts | the dominance closure lemmas (§3.2), with signs by `by intervals()` |
| `positivity` / `linarith` for `≼` | dominance goals | a combination | the closure lemmas |

The order matters. WZ comes first: it is the smallest and highest-yield of
these, and its check is an identity of rational functions. Holonomic
closure comes second, because it gives the elementary functions' identities
automatically and sits on §3.4. Gruntz belongs to the transseries instance
and comes last.

### 3.6 What is not the core

- **Synthetic differential geometry.** Its nilpotent infinitesimals make the
  derivative literally a coefficient, but the Kock–Lawvere axiom contradicts
  excluded middle and cannot sit on `CReal`. There, `d² ≈ 0` already forces
  `d ≈ 0`, so the axiom would prove `0 = 1`. It would need its own smooth
  line with a model behind it. The jets of §5 keep its algebraic content
  without the axiom. Its models are tangent categories, so they can appear
  later as instances of §3.1.
- **Paul Taylor's Abstract Stone Duality and Brouwer's continuity axioms.**
  These make every definable function continuous, which is beautiful, but
  they are axioms against excluded middle, and that would block export to
  Lean (roadmap: export is wanted more than import). They remain research.
- **Filters** (§6.1).
- **An infinitesimal surface** (the Ω-calculus of Schmieden and Laugwitz).
  Its "hyperreals" are sequences up to eventual agreement, which are exactly
  the germs at `n → ∞` of §6. Writing `ε ≈ 0` and `st(…)` could elaborate to
  witnessed `≺` statements, so it is a possible notation over this core, not
  a foundation.

### 3.7 Interfaces and instances

The two axes are filed as interfaces now (`differential-structures`,
`valued-rings-and-newton`), so that the instance layers are shaped by them.
Each interface's first round validates it on two instances that differ in
kind:

- **The differential structure** on jets and Hurwitz series (exact), then
  on `C¹` functions on `CReal` (with a remainder).
- **The dominance relation** on germs at `n → ∞` (archimedean) and on
  `ε`-adic series (non-archimedean).

The meeting-point class waits until Laurent series with `d/dx` exist as an
instance of both. An interface that two instances do not exercise is cruft,
and that is the only reason the instances are built in parallel with their
interfaces rather than after them.

## 4. Layer A: finite sums and products

**Semantics.** This takes route 2 of `big-operator-semantics`: generic
finite folds over a commutative monoid modulo its relation. Integration is
separate, and it is defined later as a limit of finite sums (§12) rather
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
  discrete mean value inequality that §7 lifts.
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

## 5. Layer B: Hurwitz series and jets

This is the representation of §3.4, made concrete. A series over a
commutative ring `A` is its coefficient function in the Hurwitz convention,
where `coeff(n)` stands for the `n`-th derivative at the point. `≈` is
taken coefficientwise.

```heather
// Sketch.
record Hurwitz<A> { coeff: Nat → A }
fn Hurwitz::Same(f, g) → Type { (n: Nat) → f.coeff(n) ≈ g.coeff(n) }
fn Hurwitz::d(f) → Hurwitz<A> { Hurwitz(λ n => f.coeff(Succ(n))) }        // the derivative is the shift
fn Hurwitz::mul(f, g) → Hurwitz<A> {
    Hurwitz(λ n => ∑_{(i,j) ∈ antidiag(n)} C(n, i) * f.coeff(i) * g.coeff(j))
}
theorem Hurwitz::coind(f, g, h0: f.coeff(0) ≈ g.coeff(0), hd: f.d() ≈ g.d()): f ≈ g     // bisimulation, by induction
```

- **Ring.** Addition is pointwise, and the product is binomial convolution,
  a Layer A sum over the antidiagonal with Layer A′'s binomial
  coefficients. Associativity is the triangle exchange of §4. The instance
  is `CommRingOfInt` at the series' `≈`, so `ring` works on series by
  #219's route. The derivative is a derivation: the Leibniz rule
  `d(fg) ≈ d(f)·g + f·d(g)` is Pascal's rule summed.
- **Definitions by ODE.** `exp.coeff(n) = 1` for every `n`. `sin` and `cos`
  have the coefficients `0, 1, 0, -1, …` and `1, 0, -1, 0, …`. A general
  `f' = F(f)` with a given head is course-of-values recursion on the
  coefficient index. The laws are coinduction (`Hurwitz::coind`):
  - `d(s² + c²) ≈ 0` with head `1`, so `s² + c² ≈ 1`, over `ℤ`;
  - `exp(x + y) ≈ exp(x)·exp(y)` in two variables, or its one-variable
    shadow `exp(a·t)·exp(b·t) ≈ exp((a+b)·t)`, since both sides satisfy
    `F' = (a+b)·F` with head `1`.
- **Polynomials and jets.** A polynomial is a series with a degree bound
  (`∃ d, ∀ n ≥ d, coeff(n) ≈ 0`, with `d` as data). `Jet(A, N)` is series
  up to order `N`, meaning `≈` on the coefficients `≤ N` only. That is a
  ring, and truncation is a ring homomorphism. All three compute at `Rat`
  and at `Int`.
- **Composition** `f ∘ g` (Faà di Bruno) is defined when `g.coeff(0) ≈ 0`.
  Only coefficients up to `n` contribute to coefficient `n` of the
  composite, so each is a finite sum. That finiteness is what transseries'
  grid-based supports generalise (§11).
- **Ordinary power series** over a `ℚ`-algebra are `a_n / n!` of a Hurwitz
  series. The isomorphism is needed for evaluation (§8) and for Cauchy's
  majorant estimates, and nowhere else.
- **Newton iteration** doubles the number of correct coefficients per
  step. It covers inverses (when `coeff(0)` is a unit), square roots, and
  simple roots of polynomial equations. It is the `ε`-adic instance of
  §3.2's Newton lemma, and §10 needs it.
- **Jets and automatic differentiation.** `Jet(A, 1)` is the dual numbers.
  Evaluating a polynomial program at `x + ε` gives `f(x) + f'(x)·ε`, which
  is the forward-mode AD theorem, and its transpose is reverse mode.
  `issues/ml-layers-reverse-mode.md` asks for "the formal derivative on
  polynomial layers", and this layer is that, as the exact instance of
  §3.1. `Jet(A, N)` is Taylor-mode AD.

This layer is also the algebraic content of synthetic differential
geometry, without its axiom (§3.6). There, `ε` with `ε² = 0` is an element
of the line. Here it lives in a quotient ring, so the "every map on `D` is
affine" property is a theorem for polynomial maps. For general maps it
holds up to `o(h)`, which is the definition of differentiability in §7.

Multivariate series (`A[[x, y]]` as `Nat × Nat → A`, or iterated) are
deferred until a customer needs more than the two-variable `exp` law.

## 6. Layer C: approaches and quantitative asymptotics

### 6.1 Not filters

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

### 6.2 Approaches

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

### 6.3 Landau relations with their witnesses

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
- **As a dominance relation.** At a fixed approach, `BigO` satisfies §3.2's
  axioms, so this layer is the archimedean instance of axis 2. The
  `ε`-adic and transseries instances share its closure lemmas' statements.

The first customer needs no real functions at all: sequences `Nat → Rat` at
`n → ∞`. That covers `Series::fine`, the regularity bounds, and statements
like `cost(n) = O(n log n)` about compiled programs, should
`heather-in-heather` want to state complexity rather than measure it.

## 7. Layer D: certified expansions and the derivative

### 7.1 The record

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
  Because `O`'s threshold and constant are data (§6.3), the asymptotic
  reading is the uniform one with the neighbourhood forgotten. One record
  serves both, and the asymptotic statement is a projection of it.

Operations on expansions (sum, product truncated at `N`, composition,
reciprocal when the leading coefficient is apart from zero) each come as a
pair: the coefficient computation, which is the jet algebra of Layer B, and
a remainder lemma, which is the closure algebra of Layer C. **The map from
an expansion to its jet is a ring homomorphism into `Jet(F, N)`, and it
sends composition to jet composition.** Each rule is a ring identity in
`Jet` plus a bound, proved once and at every order.

### 7.2 The derivative

`f` is **uniformly differentiable on `S` with derivative `g`** when one
modulus serves every point: for each `k` there is a `δ` such that `x, y ∈
S` and `|y - x| <= δ` give `|f(y) - f(x) - g(x)(y - x)| <= (1/(k+1))·|y -
x|`. That is Bishop's definition, and it is a uniform first-order expansion
of `f(x + h)` in the scale `1, h`, with the remainder `o(h)` and its modulus
independent of `x`. Order-`N` differentiability is the order-`N` expansion,
with the jet as its coefficients.

This settles the design question in `issues/real-functions-and-derivatives.md`.
Use Bishop's uniform derivative on a set (an interval first), stated as a
uniform expansion, and let it inherit everything above. This is the `C¹`
instance of §3.1's differential structure. The Lipschitz functions with the
Edalat–Lieutier interval derivative are the lax instance beside it, and
they are the one ML's subgradients need.


- The **rules** (sum, product, chain, quotient where the denominator is
  apart from zero, and Faà di Bruno at order `N`) come from §7.1.
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

## 8. Layer E: series and analytic functions

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
- **Power series with a radius.** A Hurwitz series over `Rat` whose
  ordinary coefficients have a Cauchy majorant, `|a_n| / n! <= M / r^n`
  (with `M` and `r` rational, as data), is an analytic function on
  `|x| < r`. Evaluation at a `CReal` `x` with `|x| <=
  r' < r` converges at a geometric rate fixed by `r'/r`. **The evaluation
  map is a ring homomorphism on the disc**: sums are immediate, and products
  are the Cauchy product theorem. Majorants multiply, and the product of
  two geometric tails is bounded through the triangle sums of §4.
- **The laws of the elementary functions** then need no derivatives of real
  functions. Each formal law of §5 (`exp(a + b)`, `sin² + cos²`, the
  addition formulas) maps through the evaluation homomorphism to a law at
  `CReal`. For `elementary-functions-at-reals`, this is the "Cauchy product"
  route, made generic so that it is proved once for every identity rather
  than once per identity. Real arguments come for free, because evaluation
  is defined at any `CReal` in the disc. Monotonicity of `exp` comes from
  `exp(x) = exp(x/2)²` and `exp(h) >= 1 + h` for `h >= 0`. It does not need
  the mean value theorem.
- **Uniqueness by an equation.** `exp` as the unique solution of `f' = f`,
  `f(0) = 1`, needs §7. It is a second characterisation, proved after the
  first, not the definition.

Generic coefficient carriers (complex numbers for `e^{ix}`, matrices for
`exp(A)`, jets for `exp(x + ε)`) want a complete normed commutative ring.
That class is deferred until a customer needs one: the first carrier is
`Rat` coefficients evaluated at `CReal`. `exp` on `Jet(F, N)` needs nothing
analytic at all, because `ε` is nilpotent: `exp(x + ε) = exp(x)·∑_{k≤N}
ε^k/k!`. That is how `exp' = exp` appears on the jet side.

## 9. The showcase: Euler–Maclaurin, harmonic numbers, Stirling

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

## 10. Layer F: perturbation theory

Every kind of perturbation theory here is Newton's lemma (§3.2) in one
dominance relation or another.

**Regular perturbation.** Take `F(x, ε) = 0` with `F(x₀, 0) = 0` and
`∂F/∂x` invertible at `(x₀, 0)`. The formal solution `x(ε)` is Hensel
lifting in the `ε`-adic dominance (Layer B's Newton iteration). Each
coefficient solves a linear equation with the same invertible derivative,
so it computes at `Rat`.

The analytic statement is the order-`N` expansion of the true solution
(Layer D), with remainder `O(ε^{N+1})`. Its proof is the archimedean
Newton lemma, a contraction with an explicit rate, and the rate gives the
remainder's constant. One fixed-point theorem with rates serves both sides
(§3.2). The first instances are a root of a polynomial with perturbed
coefficients, then fixed points of a parametrised contraction. Eigenvalue
perturbation waits for `finite-linear-algebra`.

**Singular perturbation.** When the derivative at the base point is not
invertible, the roots of `F(x, ε) = 0` are Puiseux series in `ε^{1/q}`. The
exponents are the slopes of the Newton polygon, which is the
tropicalisation of `F`. This is the dominance relation with monomials
`ε^ℚ`. Exponentially small terms `e^{-1/ε}` (boundary layers, tunnelling)
are not Puiseux, and they need transseries (§11).

**Perturbation of differential equations.** An ODE with a small parameter,
or an asymptotic solution at `x → ∞`, is a newtonian problem: Newton's lemma
for differential polynomials (§3.3). This is where the meeting point stops
being abstract.

**Machine-learning theory.** The effective theory of deep networks (Roberts,
Yaida and Hanin, *The Principles of Deep Learning Theory*; Wick's `PDLT`)
expands statistics of a network in `1/width`:

- the infinite-width limit (Gaussian process, NTK) is order zero;
- finite-width corrections are higher orders.

Formally that is a series in `n^{-1}`. Its meaning is a germ statement at
`n → ∞` with remainder `O(n^{-k-1})`, which is Layers C–D. The lazy-training
and NTK results are first-order perturbation of the training dynamics
around initialisation. Heather can state these over `Rat` and `CReal`
before it has any measure theory, because the expectations involved over a
finite dataset are finite sums (§4).

**Float error analysis** is first-order perturbation in `u`. The standard
model `fl(x ∘ y) = (x ∘ y)(1 + δ)` with `|δ| <= u`, and `Format::gamma_add`
(`γ_m + γ_n + γ_m γ_n <= γ_{m+n}`), is `O`-arithmetic with explicit
constants at the approach `u → 0⁺`. Nothing in `lib/std/num/float/` needs
restating. Reading "error `= n·u + O(u²)`" as a projection of the existing
`γ_n` bounds is a good probe that Layer D's records fit a mature customer.

## 11. Layer G: differential-valued fields and transseries (horizon)

A transseries is a generalised series `∑ c_𝔪 𝔪` over a totally ordered
monomial group `𝔐` built from `x`, `exp` and `log`: `x^a`, `e^x`,
`e^{x log x}`, `log log x`, and so on. Its support is small enough that
products are defined. Transseries form a newtonian H-field (§3.3) closed
under composition. Aschenbrenner, van den Dries and van der Hoeven show that
its theory as an ordered differential field is model complete and explicitly
axiomatised, so it is decidable. That makes it a complete theory of
"asymptotic analysis" in a precise sense. It is the main instance of the
meeting point. Every reasonable germ has a transseries, and the
transseries form a field.

Design consequences for Heather:

- **Grid-based, not well-based, supports.** Well-based supports (Hahn
  series, with no infinite ascending chain in the dominance order) need
  well-orders, which are constructively delicate. Grid-based supports (van
  der Hoeven) lie in `𝔪 · 𝔫₁^ℕ ⋯ 𝔫_k^ℕ` for finitely many infinitesimal
  monomials. They are finite descriptions, and each coefficient of a
  product is a finite sum. That is the finiteness that makes composition
  work in Layer B, and it is the computational choice.
- **The leading term is data** (§3.2). The order is the sign of the leading
  coefficient, so positivity is witnessed by a monomial below which
  coefficients are `≈ 0` and a positive coefficient there.
- **Build the tower in steps.**
  - Laurent series (`𝔐 = ℤ`) with `d/dx`. These are the first computable
    differential-valued field and the first instance of both axes at once.
  - Puiseux series (`ℚ`).
  - `x^a log^b x`.
  - Exponentials, where closure needs the transfinite tower.

  Each step has a customer of its own, and the first two serve singular
  perturbation (§10).
- **Automation.** Gruntz's algorithm (§3.5) computes limits of exp-log
  expressions by expanding them in this field. Certifying it is the
  transseries layer's equivalent of `omega`.
- **The hook to leave now.** Write Layer B's convolution as a sum over a
  named `antidiag(n)`, the list of factorisations of `n` in the monomial
  monoid. Transseries replace `Nat` and `antidiag` with a grid and its
  finite factorisation lists. Layer B should not be generic over the monoid
  in its first round, which would cost every client for a customer years
  out, but the name keeps the substitution mechanical.

The customers are Wick's asymptotics research (Gevrey series, Borel
summation), asymptotics of recurrences, and the ADH theory itself as a
long-term mathematics showcase. This is research, filed so that the earlier
layers are shaped by it, not scheduled.

## 12. Integration, briefly

Integration is not one of these layers, but they decide its first form. A
uniformly continuous function on `[a, b]` (with its modulus as data) has a
Riemann integral as the limit of range sums over uniform partitions. The
tail modulus comes from the continuity modulus, and the limit is a
`CReal::lim`. That is Bishop's integral. It is Layer A plus Layer C, and it
gives the fundamental theorem of calculus against §7's derivative by
telescoping (Layer A′ again). Measure-theoretic integration, and the
counting-measure view of `∑`, stay with `big-operator-semantics` and the
measure work (roadmap mathematics item 4). This route does not compete
with them: Riemann sums are simple-function integrals.

## 13. Order of work

Each step names what it unblocks. The slugs are the issues filed with this
note.

| # | Issue | Part | Needs | Unblocks |
|---|---|---|---|---|
| 1 | `finite-sums-and-products` | A | semiring layers (done) | everything below, plus `finite-linear-algebra`'s `Fin n` sums |
| 2 | `finite-difference-calculus` | A′ | 1 | binomial convolution (3), geometric tails (8), mean value inequality (7) |
| 3 | `formal-power-series` | B (Hurwitz) | 1, 2, `ring` at `≈` (#219) | `exp`/`sin`/`cos` and their laws formally, the formal derivative for `ml-layers`, Newton lifting |
| 4 | `asymptotic-relations` | C | `CReal` (done), 1 | limits, continuity, `math-reals`' "sequences, limits, continuity" |
| 5 | `differential-structures` | axis 1 | 3, then 7 | one chain rule for every instance; reverse mode for `ml-layers` |
| 6 | `valued-rings-and-newton` | axis 2 | 3, 4 | one Newton lemma (Hensel and Kantorovich); perturbation (11) |
| 7 | `certified-expansions` | D | 4, 3 | the `CReal` derivative (`real-functions-and-derivatives`), Taylor's theorem, `asymp` |
| 8 | `power-series-evaluation` | E | 2, 3, 4 | `elementary-functions-at-reals`' laws, real arguments, rebasing `Series` |
| 9 | `wz-certificates` | §3.5 | 1, 2, `field-simp` | hypergeometric sum identities by certificate |
| 10 | `holonomic-closure` | §3.5 | 3, 9 | ODE- and recurrence-defined identities by certificate |
| 11 | `regular-perturbation-expansions` | F | 6, 7 | perturbed roots and fixed points, the float error reading, width expansions |
| 12 | `taylor-model-enclosures` | D (uniform) | 7, intervals (#208) | tighter `by intervals()` over ranges, `float-transcendental` specs |
| 13 | `harmonic-and-stirling-asymptotics` | showcase | 7, 8, `log` | the first divergent expansion, and γ |
| 14 | `grid-based-transseries` | G, meeting point | 5, 6, 11 | research horizon: differential-valued fields, Gruntz |

Items 1–4 can run in parallel once item 1's range sum exists. Items 5 and 6
are the interfaces. Each is validated by two instances in its first round
(§3.7), and that is why each needs item 3 and then a `CReal` instance. Item
3 has an outside customer waiting (`ml-layers`). Items 7 and 8 are what
`math-reals` waits on in substance. Item 9 can start as soon as item 2
lands and does not block anything, which makes it a good parallel lane in
the `tactics` area.

**On the roadmap.** `docs/roadmap.md` puts "asymptotics and transseries" at
item (5) of the mathematics order, after measure. This note argues that the
foundational part (items 4–7 above) is what item (2)'s `math-reals`
milestone, "sequences, limits, continuity", consists of. On that reading it
moves up beside the reals, and only the transseries horizon (item 14) stays
at (5). That is a ranking change, which is Minus's call, so the roadmap's
order is not edited here.

## 14. Decisions this note makes, and the ones it leaves

Made here. Each is revisable when a customer pushes back.

- **Two axes and a meeting point**, differential structure and dominance,
  as the core. The concrete layers are their first instances (§3).
- **A derivative is data.** A differentiable map is a map paired with its
  derivative and evidence (§3.1), and smoothness is coinductive.
- **Smallness is a dominance relation without totality**, with leading
  monomials as data (§3.2). Newton's lemma is one contraction theorem with
  rates.
- **Calculus in coinductive form, taken as a method**: the Hurwitz
  convention, coefficient functions, and bisimulation as a theorem.
  Codata comes later (§3.4).
- **Decision procedures emit certificates**, in the order WZ, holonomic,
  Gruntz (§3.5).
- **Countable nested approaches**, not filters (§6.1–6.2). Landau constants
  are `Rat`, moduli are `Nat → Nat`, and there is no division in `~`
  (§6.3).
- **Bishop's uniform derivative** is the `CReal` instance (§7.2), and the
  Edalat–Lieutier interval derivative is the lax Lipschitz instance (§3.1).
- **Formal identities first, then the evaluation homomorphism**, for the
  laws of the elementary functions (§8).
- **Grid-based supports** for transseries (§11).
- **No synthetic axioms** (SDG, ASD, continuity) in the core (§3.6).

Left open:

- The roadmap move in §13.
- How the differential-structure interface is encoded: a class over a
  category record (objects, homs) or over an evidence predicate on plain
  functions. The second is simpler and probably enough for the Cartesian
  case. Tangent categories need the first.
- When non-Cartesian (tangent) structure is wanted. Decide at the first
  manifold customer.
- Multivariate Hurwitz series, iterated or multi-index. Decide at the first
  two-variable customer.
- The normed-ring class for generic series carriers (§8). Decide at the
  first non-`Rat` coefficient customer.
- The surface spelling of `∑` before the binder production lands.

## 15. Non-goals

- No change to `CReal`'s representation, to `Series`'s exported statements,
  or to the kernel.
- No new notation production. `∑ k < n, f(k)` waits for
  `notation-extensibility`.
- No filters, no ultrafilters, no nonstandard analysis, and no synthetic
  axioms (§3.6).
- No measure theory here. §12 states only the integral that falls out.

## References

- E. Bishop and D. Bridges, *Constructive Analysis* (1985), ch. 2 (uniform
  derivative, integral) and ch. 5 (moduli).
- R. Blute, R. Cockett and R. Seely, "Cartesian differential categories",
  *Theory and Applications of Categories* 22 (2009).
- R. Cockett and G. Cruttwell, "Differential structure, tangent structure,
  and SDG", *Applied Categorical Structures* 22 (2014).
- R. Cockett, G. Cruttwell, J. Gallagher, J.-S. P. Lemay, B. MacAdam,
  G. Plotkin and D. Pronk, "Reverse derivative categories", CSL 2020.
- G. Cruttwell, B. Gavranović, N. Ghani, P. Wilson and F. Zanasi,
  "Categorical foundations of gradient-based learning", ESOP 2022.
- T. Ehrhard and L. Regnier, "The differential lambda-calculus", *TCS* 309
  (2003).
- A. Edalat and A. Lieutier, "Domain theory and differential calculus
  (functions of one variable)", *MSCS* 14 (2004).
- D. Pavlović and M. Escardó, "Calculus in coinductive form", LICS 1998.
- W. Keigher, "On the ring of Hurwitz series", *Communications in Algebra*
  25 (1997).
- J. Blanchette, A. Popescu and D. Traytel, "Foundational extensible
  corecursion", ICFP 2015.
- M. Rosenlicht, "Differential valuations", *Pacific J. Math.* 86 (1980).
- J. van der Hoeven, *Transseries and Real Differential Algebra*, LNM 1888
  (2006): grid-based transseries.
- M. Aschenbrenner, L. van den Dries and J. van der Hoeven, *Asymptotic
  Differential Algebra and Model Theory of Transseries* (2017).
- M. Petkovšek, H. Wilf and D. Zeilberger, *A = B* (1996).
- D. Gruntz, *On Computing Limits in a Symbolic Manipulation System*, ETH
  thesis (1996).
- D. Roberts, S. Yaida and B. Hanin, *The Principles of Deep Learning
  Theory* (2022).
- J. Dieudonné, *Calcul infinitésimal* (1968): développements limités and
  asymptotic scales.
- R. Graham, D. Knuth and O. Patashnik, *Concrete Mathematics*, ch. 2 and 9.
- N. G. de Bruijn, *Asymptotic Methods in Analysis*: Euler–Maclaurin,
  Stirling.
- K. Makino and M. Berz, "Taylor models and other validated functional
  inclusion methods" (2003).
- U. Kohlenbach, *Applied Proof Theory* (2008): moduli and rates as the
  computational content of analytic statements.
- A. Kock, *Synthetic Differential Geometry* (2nd ed. 2006).
