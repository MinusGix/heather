# Nonlinear arithmetic: one certificate, searches by cost

Date: 2026-10-28. Owner:
[nlinarith-products-of-facts](../../issues/nlinarith-products-of-facts.md).
Follow-ups: [linarith-simplex-search](../../issues/linarith-simplex-search.md),
[sos-certificate-oracle](../../issues/sos-certificate-oracle.md),
[interval-variable-boxes](../../issues/interval-variable-boxes.md).

`linarith` reads products as monomials and combines facts linearly
(docs/tactics/linarith-design.md §3, §8), so it refuses `0 <= x * x`, and
`0 <= a * b` from `0 <= a` and `0 <= b`
(`lib/_tests/std/tactic/linarith_tests.hthr`: `int_square_is_not_linear`,
`creal_product_is_not_linear`). This note chooses how Heather proves
polynomial inequalities. It compares Lean's `nlinarith` heuristic with
Positivstellensatz certificates found by semidefinite programming, cylindrical
algebraic decomposition, interval branch-and-bound and an untrusted external
oracle in the style of `polyrith`.

**The decision.** Every method that yields a certificate Heather can check
gives the same kind of certificate: a sum of nonnegative products, equal to
the goal's difference by a `ring` identity (§2). The methods differ only in
how they find the products. So Heather builds the checker once, as an
extension of `linarith`'s certificate, and adds searches in order of cost:

1. **`nlinarith` now** (§4). It adds pairwise products of the facts and the
   squares the problem shows, then runs `linarith`'s search. Hints cost
   nothing extra: a fact argument is any expression, so
   `nlinarith(h, Rat::sq_nonneg(a - b))` already passes a square as a hint.
2. **An exact simplex search** under `linarith` once the product rows
   outgrow Fourier–Motzkin (§6).
3. **Sums of squares by SDP, later and offline** (§5). An untrusted tool
   finds the squares and prints them as hint text that is pasted into the
   source. The gate never runs a numerical solver.

CAD is declined (§7). Interval branch-and-bound is not a rival. It covers a
different set of goals (strict, bounded, transcendental), so it is filed as
its own extension of `by intervals()` (§8).

## 1. What clients need

The library's nonlinear inequalities fall into three shapes:

- **Monotonicity of products**: `a·c <= b·d` from `a <= b`, `c <= d` and
  signs. Examples are `OrderedSemiring::mul_le_mul`, `Rat::mul_le_mono_r`, the
  float error bounds in `lib/std/num/float/round.hthr` and the containment
  lemmas in `interval.hthr`. These are products of two facts.
- **Squares**: `0 <= x·x`, `2ab <= a² + b²`, and regularity estimates where an
  error term multiplies a bound. These are a square, or a square plus linear
  facts.
- **Case analysis on signs**: `Rat::mul_nonneg_approx` splits on
  `Rat::le_total` twice. No method below removes the split at `CReal`, where
  `le_total` does not hold. At `Rat` and `Int`, a split followed by
  `nlinarith` in each case is the composition.

Each shape is degree two in the facts, and the first two need no search
beyond products of the facts and the squares. That is exactly what
`nlinarith`'s heuristic produces.

## 2. The certificate

Take a goal `a R b` and facts `loᵢ Rᵢ hiᵢ` at one carrier. Each fact gives a
**part** `pᵢ = hiᵢ − loᵢ`, which is `≥ 0` or `> 0`. A **product part** is
built from parts by the order laws:

| part | proved by | sign |
|---|---|---|
| `pᵢ·pⱼ` | `OrderedSemiring::mul_nonneg` / `mul_pos` (`Int::`, `Nat::` at those) | `> 0` if both strict, else `≥ 0` |
| `t·t` | `sq_nonneg(t)` (new, §4.5) | `≥ 0` |
| `m` with even exponents (`x²y²`) | `sq_nonneg` of its root | `≥ 0` |
| a hint `h: 0 <= e` / `0 < e` | the hint itself | as written |

The certificate is linarith's direct form over these parts:

```text
K·(b − a) ≈ Σ λᵢ·Pᵢ + c        K > 0,  λᵢ > 0,  c ≥ 0
```

`ring` proves the identity at the carrier, so the certificate is still one
`ring` identity plus one lemma application per part. A product part is a fact
with a richer proof, nothing more. This is the degree-bounded
Positivstellensatz cone, and every method in §3 that produces a certificate
produces one of this form. The methods differ only in which `Pᵢ` they offer.

**Refutation where it is valid.** In the direct form the negated goal can be
used only linearly, scaled by `K`. A product of the negated goal with a fact
would make `K` a polynomial that is only `≥ 0`, and that proves nothing. Both
Mathlib's `nlinarith` and Coq's `nra` multiply the negated goal, which is how
`a <= b` follows from `a·c <= b·c` and `0 < c`, so Heather wants that too.
The refutation form has it, and it is valid wherever the goal is a negation:

- `a <= b` is `¬(b < a)` at every carrier, including `CReal`, where
  `le_of_not_lt` is a class law. So `nlinarith` assumes `g: b < a`, makes
  `a − b > 0` a strict part like any other, and proves `False` by
  `lin_finish_false`.
- `a ≈ b` is two `<=` goals. `¬(a < b)`, `False` and contradictory facts need
  no change.
- `a < b` at `Rat` and `Int` uses decidability: `Rat::lt_of_not_le` and
  `Int::lt_of_not_le` turn a refutation of `b <= a` into `a < b`.
- **`a < b` at `CReal` stays direct.** There `<` is positive data, and a
  refutation proves only `¬¬(a < b)`. The goal row is used linearly (or
  scaled by positive denominators, as in linarith-design §5), never multiplied
  by a fact. A client who needs that product supplies it as a hint. This is
  the one place where constructive reals constrain the search, and the
  refusal says so.

## 3. The methods compared

| method | finds | complete? | certificate | at `CReal` | cost to build |
|---|---|---|---|---|---|
| `nlinarith` heuristic (Mathlib; Coq `nra`) | products of pairs of facts and squares the problem shows, then LP | no | §2 | yes (§2's rule) | small: §5's `Use` machinery generalized |
| hints as facts | whatever the author names | no | §2 | yes | none: `linarith(…)` already takes expressions |
| SOS by SDP (Coq `psatz`, HOL Light `REAL_SOS`, Isabelle `sos`) | squares of arbitrary polynomials up to a degree | for Positivstellensatz degree `d` | §2 after rounding to ℚ | yes | large: an SDP solver and exact rounding |
| `polyrith`-style external oracle | equalities by Gröbner bases | ideal membership | a `linear_combination` | yes | network/process dependence; `ring(h)` already searches |
| CAD (QEPCAD, Tarski) | sign-invariant cells | yes, for real closed fields | none compact | no | very large, doubly exponential |
| interval branch-and-bound (CoqInterval, Flyspeck) | enclosures on subdivided boxes | strict goals on bounded boxes | evaluation verdicts | yes (`RealExpr`) | moderate, on `by intervals()` |

**`nlinarith`.** Mathlib's preprocessing adds, for every pair of
comparisons `t₁ R₁ 0`, `t₂ R₂ 0` (the negated goal among them), the product
`t₁·t₂ R 0`, and adds `t² >= 0` for every `t` with `t^2` or `t*t` in the
input. Then it runs `linarith` (since 2024 by simplex). Coq's `nra` does the
same over Micromega's checker. Both are incomplete and cheap to run. They
cover the usual monotonicity goals, and hints are the escape hatch
(`nlinarith [sq_nonneg (a - b)]`). For Heather it
is mostly built already. `linarith` reads monomials through `ring`'s reader,
§5's `Use` multiplies a row's form by a factor's form, and the certificate
takes any proved part.

**SOS by SDP.** A Positivstellensatz certificate of degree `d` asks for
polynomials `σ` that are sums of squares, with `p = σ₀ + Σ σᵢ·gᵢ + …`.
Finding the `σ` is a semidefinite program. Coq's `psatz` and HOL Light's
`REAL_SOS` call the external solver CSDP, round its floating-point answer to
rationals, and check the result exactly. This search finds squares that the
problem does not show, such as `x⁴ − 2x²y + y² + x² = (x² − y)² + x²` without
the hint. That is its whole advantage over the heuristic, and nothing in the
library needs it yet. Its costs are an interior-point solver, rounding that
can fail on goals tight at the boundary, and answers that can differ between
machines. Heather's library gate wants a deterministic accept. §5 keeps the
benefit and drops that last cost, the same way Isabelle's `sos` replays a
stored certificate without the solver.

**`polyrith`.** Lean's `polyrith` sends equalities to Sage, which computes a
Gröbner basis, and prints a `linear_combination` to paste into the source.
For equalities Heather has the in-tree half already: `ring(h…)` searches for
polynomial multipliers (docs/tactics/ring-normalization-design.md §4) and checks
`T = Σ cᵢ·Hᵢ`. It is bounded, not Gröbner-complete, and so far it has been
enough. What `polyrith` contributes to this design is the workflow: the
untrusted oracle runs outside the build and writes source, and the source
alone is checked. §5 adopts that workflow.

**CAD.** Cylindrical algebraic decomposition decides the first-order theory
of real closed fields, so it is the only complete method on the list. It is
declined for three reasons, each sufficient on its own (§7).

**Intervals.** `by intervals()` proves closed comparisons by evaluating
enclosures. With variables confined to boxes by facts and the boxes bisected
(§8), it proves strict inequalities on bounded domains, transcendental ones
included, which none of the algebraic methods can. It cannot prove a tight
goal such as `0 <= x·x` at `x = 0`, and it cannot use an unbounded variable.
So it complements `nlinarith` and does not replace it.

## 4. `nlinarith` in Heather

### 4.1 What a client writes

```heather
theorem sq(x: Int): OfNat(0) <= x * x { nlinarith }
theorem prod(a, b: CReal, ha: 0 <= a, hb: 0 <= b): 0 <= a * b { nlinarith(ha, hb) }
theorem mono(a, b, c: Rat, h: a <= b, hc: 0 <= c): a * c <= b * c { nlinarith(h, hc) }
theorem amgm(a, b: Rat): 2 * (a * b) <= a * a + b * b { nlinarith(Rat::sq_nonneg(a - b)) }
```

The name is separate from `linarith`, and `linarith` does not try products.
Products multiply the search's input by the square of the number of facts,
and `linarith`'s cost should stay what a reader predicts from the facts. When
`linarith` refuses a problem whose reading contains a nonlinear monomial, the
refusal says that `nlinarith` may prove it.

### 4.2 The products

- **Which facts multiply.** The goal's negation (where §2 allows it) and
  the written facts are multiplied pairwise, each with itself included. That
  is `k(k+1)/2` products for `k` rows. When those find nothing, the second
  pass adds the context's facts, as `linarith` does, and multiplies them too,
  so `nlinarith` with no arguments works. Either way at most 12 rows are
  multiplied (`MAX_PRODUCT_ROWS`), taking the negation first, then the
  written facts, then the context's.
- **Squares.** The reader (`FieldReading::squares`) records the base of every
  product whose two factors read as one nonconstant polynomial (`t * t`,
  `(a - b) * (a - b)`), before normalization, because `(a − b)²` normalizes
  to a shape that no longer shows the square. Each monomial in the problem
  whose exponents are all even is also offered as the square of its root.
  Both are cheap and need no search. `npow` is an atom to `ring`, so
  `x.npow(2)` is not read as a square.
- **Degree.** Products are of two parts, so the degree is two in the facts.
  A third factor comes from a hint, which is a fact and therefore multiplies.
  A `degree` knob waits for a client (Mathlib's default is two as well).

A product row's form is the polynomial product of its two parts' forms over
`ring`'s monomials, computed as `scale` already does for denominators. The
search treats each new monomial as a variable.

### 4.3 The certificate's text

The parts are generic lemmas in `lib/std/tactic/linarith.hthr`, stated over
the differences `hi + -lo` that `linarith` already writes, so the existing
`lin_scale_*`, `lin_add_*` and the one `ring` identity are reused unchanged:
`nlin_mul_le` (a strict part weakened first by `lin_weaken`), `nlin_mul_lt`,
and `nlin_sq`. A product's form is its two parts' forms multiplied out
(`FieldReading::product`); a square's base is written over the atoms' aliases
(`Problem::form_source`). `nlin_le_of_refute` is `le_of_not_lt`: the
certificate for `a <= b` is

```text
linarith::nlin_le_of_refute<C>(a, b, λ __nlin_g => <certificate of False>)
```

with `__nlin_g: b < a` a row like a written fact, its part
`lin_lt_part(b, a, __nlin_g)`. `¬(a < b)` is the `λ` alone, `a ≈ b` two
refutations, and a strict goal at `Rat` goes through `Rat::lt_of_not_le`.

### 4.4 At `Int` and `Nat`

`linarith`'s integral route hands `omega` the facts and one `ring` bridge per
multiplying side (linarith-design §8). `nlinarith` adds, for each pair of
orders among the goal's negation and the facts (`<=`, `<`, and their
negations through `le_of_not_lt`/`lt_of_not_le`), two more `let`s:

```text
let __nlin_p0: (int::OfNat(0) <= (b - a) * (d - c)) = linarith::nlin_int_le_le(a, b, c, d, h₁, h₂);
let __nlin_q0: ((b - a) * (d - c) = <monomials>) = ring;
```

`omega` reads the product as one atom by its spelling, the same in both, and
the bridge ties it to the monomials. At `Int` each square the terms write
(and each monomial with only even exponents) gets the same pair, from
`nlin_int_sq`. A goal `a <= b` or `a < b` (or a negated one) is read back
through `Int::le_of_not_lt`/`lt_of_not_le` (`Nat::` at `Nat`) with `omega`
proving `False` under `λ __nlin_g`, since `omega` negates the goal
internally and cannot be handed a product of its own negation.

At `Nat` a part cannot be a difference, because subtraction truncates. The
product of `a <= b` and `c <= d` is stated with its four terms on the sides
where they are positive, `a·d + b·c <= a·c + b·d` (`nlin_nat_le_le`). A strict
fact's low side is `a + 1` (`nlin_nat_lt_le` etc.), so a product with a
strict fact stays strong enough to cancel a positive factor. No squares at
`Nat`: its atoms are nonnegative to `omega` already.

### 4.5 Library lemmas the round adds

- `OrderedRing::sq_nonneg(x): 0 <= x * x`. It is constructive. Suppose
  `h: x·x < 0`. If `x < 0`, then `0 < x·x` (a product of negatives), which
  contradicts `h`. So `¬(x < 0)`, so `0 <= x` by `le_of_not_lt`. Then
  `0 <= x·x` by `mul_nonneg`, which contradicts `h` again. No decision on the
  sign of `x` is made.
- Concrete forms that a hint can name without a section: `Rat::sq_nonneg`,
  `CReal::sq_nonneg`, `Int::sq_nonneg`, and `Int::mul_nonneg`.

### 4.6 Refusal

The refusal lists the facts as they were read, as `linarith`'s does, says
that the pairwise products and the shown squares were tried, and at `CReal`
with a `<` goal says that the goal's negation was not multiplied and why. It
gives the hint spelling (`CReal::sq_nonneg(a - b)`). `linarith`'s own refusal
names `nlinarith` when its reading has a product in it.

## 5. Sums of squares: the offline oracle

Deferred until a library goal defeats both the heuristic and a short hint
list ([sos-certificate-oracle](../../issues/sos-certificate-oracle.md)). When it
lands, its shape is:

- A command, not a tactic step:
  `heather suggest-squares <file> --only <decl>`. It reads the goal as
  `nlinarith` does, poses the Positivstellensatz SDP at degree `d` over the
  monomial basis, solves it numerically, rounds to rationals, and checks the
  identity exactly in Rust. It prints the
  `nlinarith(h…, sq_nonneg(t₁), mul_nonneg(…))` text to paste.
- The gate replays the pasted text, which is an ordinary `nlinarith` call
  whose hints make the search trivial. Heather never runs a numerical solver
  while checking. A library that depends on floating point accepts or refuses
  the same way on every machine. The oracle can live outside the workspace's
  dependency policy, which permits crates above the kernel anyway (a pure-Rust
  conic solver such as Clarabel, or an external CSDP process).
- Because the output is source, a reader can see which squares a proof uses.
  That is the property `polyrith` and Isabelle's stored `sos` certificates
  have, and the one that makes an untrusted oracle harmless.

## 6. The search engine

`linarith` eliminates by Fourier–Motzkin and gives up past 2048 rows. With
products the input grows from `k` rows to `k + k(k+1)/2`, and the monomials
grow with it. Fourier–Motzkin is doubly exponential in the worst case. Exact
simplex over ℚ (Bland's rule, `Z`-scaled rows, the Farkas multipliers read
off the final tableau) finds the same `λ` in polynomial time in practice.
Mathlib moved `linarith`'s default oracle to simplex for this reason.
[linarith-simplex-search](../../issues/linarith-simplex-search.md) owns it. The
certificate does not change: the search is untrusted, and `ring` checks the
identity it writes. The round that builds `nlinarith` keeps Fourier–Motzkin
and files the first refusal it meets at the row bound as that issue's
customer.

## 7. Declined: CAD

1. **No compact certificate.** CAD's evidence is the cell decomposition with
   the sign of every polynomial on every cell. Checking it in the kernel
   means re-deriving the decomposition, including real root isolation of
   algebraic numbers. The proof-producing CADs that exist in other provers are
   large formalizations, not certificate checkers. Everything else in
   Heather's arithmetic is a search outside the kernel plus a small check
   inside it, and CAD does not fit that shape.
2. **Not constructive at `CReal`.** CAD decides the sign of a polynomial at a
   sample point, and at `CReal` that is `x < 0 ∨ x ≈ 0 ∨ 0 < x`, which does not
   hold. Positivstellensatz certificates are identities plus nonnegative
   terms, so they hold at every `OrderedField`.
3. **Cost.** CAD is doubly exponential in the number of variables, whereas
   the clients in §1 need degree two in a handful of facts.

Completeness is not worth those three costs. If a client ever needs a
quantified real statement decided, the route is an SOS or Positivstellensatz
certificate for each case it produces, not CAD in the trusted path.

## 8. Intervals over variable boxes

`by intervals()` refuses a leaf that does not compute, which includes every
variable. Facts `lo <= x <= hi` with numeral bounds make `x` an interval
leaf, and bisecting the widest variable until every box gives a verdict
proves a strict goal on the box. The certificate is a tree of `lt_of_search`
verdicts, one per box, joined by a lemma that the boxes cover the domain
([interval-variable-boxes](../../issues/interval-variable-boxes.md)). It
reaches what `nlinarith` cannot: a strict polynomial bound whose certificate
the heuristic does not find, such as `x³ − x + 1 > 0` on `[-1, 1]`,
and later transcendental bounds once the elementary enclosures take an
interval argument. It fails where `nlinarith` succeeds: tight goals and
unbounded variables. The cost is exponential in the number of variables
bisected. Taylor-model enclosures, as Flyspeck used, are the known lever
if dimension ever matters.

## 9. Cost shape

The certificate is `linarith`'s: one `ring` identity and one lemma
application per part. With products the identity's degree doubles, so
`ring`'s normalization works over more monomials, which is quadratic in the
monomials of the multiplied parts. The search's input is quadratic in the
written facts. Neither depends on context facts that the products do not use.
