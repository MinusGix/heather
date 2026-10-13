# `ring`: commutative-ring normalization by reflection

Date: 2026-10-12. Owner: [ring-normalization](../issues/ring-normalization.md).
The client that asked for it is the rationals round
([setoid-rationals-round](setoid-rationals-round.md), "Where the proof text
went"): a third of `lib/std/rat.hthr` was monomial rearrangement.

- [`lib/std/ring.hthr`](../lib/std/ring.hthr): the syntax, the normalizer and
  its soundness proof, checked once.
- `crates/elab/src/ring.rs`: the tactic — reification, the multiplier search,
  the certificate.
- `crates/elab/tests/lib_std_ring.rs`: the tactic's tests and negative
  controls; `lib_std_rat.rs` checks the rewritten laws.

## 1. What a client writes

```heather
import ring;

theorem squares(a, b: Int): (a + b) * (a - b) = a * a - b * b { ring }

theorem succ(x: Nat): Succ(x) * Succ(x) = x * x + 2 * x + 1 { ring }

// With equations: `ring` finds the multipliers.
theorem Rat::add_respects(x, x2: Rat, hx: x ≈ x2, y, y2: Rat, hy: y ≈ y2):
    x + y ≈ x2 + y2
{
    ring(hx, hy, x.den.mul_int(y.den), x2.den.mul_int(y2.den))
}
```

`ring` proves an equation at `Int` or `Nat` that holds in every commutative
ring (semiring at `Nat`). `ring(h₁, …, hₖ)` proves one that follows from the
equations `hᵢ` by multiplying each by a polynomial and adding:
`lhs − rhs = Σ cᵢ·(aᵢ − bᵢ)`. The `cᵢ` are the tactic's to find; the
author names only the equations. That is what made the rational laws one line
each: `add_respects` needs `hx` scaled by `q·q′` and `hy` by `p·p′`, and the
two `mul_int` facts read the product denominators as products.

A goal or hypothesis that is a defined proposition is unfolded to the
equation it stands for, so `x ≈ y` at `Rat` is read as its
cross-multiplication. A field read off a value that computes to a
constructor is read as the field: `(x + y).num` is the numerator `Rat::add`
builds. Everything else that is not `+`, `-`, `*`, unary `-`, a numeral or
`Succ` is an atom, and two atoms that are convertible by a bounded check are
one atom — `(x + y).den.int()` in the goal and `x.den.mul(y.den).int()` in
a hypothesis.

`ring` follows the bare-form shadowing rule of `omega`, `decide` and
`positivity`: a local, alias or global named `ring` wins.

## 2. Why reflection, and what is trusted

The issue left the choice open between a Rust-side certificate of
`mul_assoc`/`mul_comm` steps (omega's contract) and an in-language normalizer
proved once. The retired `arith` measured the first: its cost was dominated
by reassociation and by composing permutation chains
([certifying-arithmetic-automation-design](certifying-arithmetic-automation-design.md),
"Cost anatomy"), and a ring certificate would be the same chains with
products. So this is the second.

The certificate for an identity is one term:

```text
ring::RingExpr::sound(__ring_atoms, ⟦lhs⟧, ⟦rhs⟧, refl)
```

`RingExpr::sound(xs, a, b, h: a.norm() = b.norm()): a.eval(xs) = b.eval(xs)`
is proved in the library. The kernel checks two things: `refl`, by evaluating
`norm` on two closed syntax trees whose only open parts are the atoms it
never looks at; and that `a.eval(xs) = b.eval(xs)` converts to the goal,
which unfolds `eval` back into the goal's own spelling. The Rust side decides
nothing. A reifier bug can make `ring` refuse a true goal or build a
certificate the kernel rejects; it cannot prove a false one.

With hypotheses the certificate is

```text
ring::RingExpr::sound_with(__ring_atoms, ⟦lhs⟧, ⟦rhs⟧, D, HD, refl)
```

where `D = Σ RMul(⟦cᵢ⟧, RSub(⟦aᵢ⟧, ⟦bᵢ⟧))`, `HD : D.eval(xs) = 0` is built
from `RingExpr::hyp` (one per used hypothesis) and `RingExpr::hyp_add`, and
`refl` is `RSub(⟦lhs⟧, ⟦rhs⟧).norm() = D.norm()`. The multipliers are
data the search found; a wrong one is refused by that `refl`.

## 3. The normal form

`RingPoly` is a list of `PTerm(c, m, rest)`, a coefficient times a
monomial, where a monomial is a dense exponent vector over the atom list
with no trailing zero. The list is sorted by the lexicographic order on
vectors, a shorter one first, and has no zero coefficient. That order is the
order of the vectors padded with zeros (a vector with no trailing zero that
extends another has a nonzero entry past it), and padding order is preserved
by adding a fixed vector, so `scale` — one term times a polynomial — keeps a
normal form sorted without re-sorting. `add` is a merge, `mul` is a sum of
`scale`s.

**Only completeness depends on the order.** Every soundness lemma holds
whatever order the comparison picks. The comparison says what it promises
through `RingPoly::Same(o, m, n)`, a type that is `m = n` at `RSame` and a
trivially true `m = m` otherwise, so no proof needs constructor
disjointness, and the one fact the merge needs — equal vectors have equal
monomials — comes from `cmp_same`. A mistake in `cmp` could only make two
equal polynomials print differently.

Two choices kept the proof small, and each was about the proof rather than
the computation:

- **Merging with the recursion split in two.** `add`'s natural definition
  recurses on either argument depending on the comparison, which is not
  structural. `add(p)` recurses on `p` and hands the merged tail to
  `add_into`, which recurses on `q` alone. Each soundness lemma is then
  induction on one list.
- **The comparison result as an argument.** `add_step(o, …)` takes the
  comparison's result and the three possible continuations, so its lemma is a
  `match` on a variable. The continuations are not evaluated unless taken
  (the kernel's values are lazy, `crates/kernel/DESIGN.md` "Sub-structures
  are lazy").

Hypotheses whose types depend on a matched variable are taken after the
match (`→` in the statement, `λ h =>` in each arm), the workaround
[elab-match-refines-hypothesis-kernel-rejects](../issues/elab-match-refines-hypothesis-kernel-rejects.md)
records.

**`Nat` goes through `Int`.** `RingNat` has no subtraction or negation and
evaluates in `Nat`. `RingNat::lift` maps it to `RingExpr`, and `eval_lift`
says `OfNat(e.eval(ys)) = e.lift().eval(lift_atoms(ys))`. A `Nat` identity is
the `Int` one at the lifted atoms, read back by `toNat`. Hypotheses at `Nat`
are combined in `Int` the same way, so the combination may use negative
multipliers even though no `Nat` term is negative.

## 4. The multiplier search

Finding `cᵢ` with `T = Σ cᵢ·Hᵢ` (`T = lhs − rhs`, `Hᵢ = aᵢ − bᵢ`) is ideal
membership, which in general wants Gröbner bases. What the clients need is
narrower: each hypothesis is used scaled by monomials that a monomial of the
target, or of an earlier scaled hypothesis, reveals. The search proposes the
candidate `(i, m)` wherever a monomial of `Hᵢ` divides a monomial that has to
cancel, adds the monomials `m·Hᵢ` introduces to the frontier, and after each
round solves the linear system `Σ x₍ᵢ,ₘ₎·(m·Hᵢ) = T` over ℚ by Gauss–Jordan
elimination. A chain of substitutions (`D = p·QR`, `QR = q·r`) is found one
link per round. It is bounded at four rounds and a fixed number of unknowns,
and a solution whose entries are not integers is refused rather than scaled:
cancelling a scalar would need a nonzero side condition no client has needed.

The search checks its own answer (`Σ cᵢ·Hᵢ = T` in the Rust polynomials) so a
searcher bug surfaces as an internal error rather than a `refl` failure. The
kernel checks it again.

When nothing is found, the error names the residual polynomial — `ring`
alone reports how the two sides differ (`differ by 2 * a * b`), `ring(h)` that
no combination of the given equations accounts for it.

## 5. What the rationals cost now

`Rat::add_assoc`, `add_respects`, `mul_respects`, `mul_add_distr` and
`add_neg` are each one `ring` call. `same_trans` keeps its cancellation and
gets its scaled equation from `ring(hxy, hyz)`. `cross_term` and the
seven-factor `distr_monomial` are gone: they existed only to feed the
hand-written proofs.

Measured with `scripts/perf ab --source-patch` over `lib/std/rat.hthr`, cold
(counters are exact; seconds are this box's and are stated as shapes):

- The module's own declarations check faster than before: the hand
  proofs' elaboration (the `calc` chains and the `omega` calls with products
  as atoms) is what went, and it was the larger part of their cost.
- Its kernel gate is dearer. The laws that were cheap chains of named lemmas
  (`mul_respects`, `add_respects`, `same_trans`) now evaluate `norm` at
  degree-four polynomials over ten-odd atoms, and that evaluation is the
  gate's new cost; `add_assoc` and `add_neg` got cheaper in the gate too.
- `ring.hthr` itself is a new dependency, checked once per library build
  (module images cache it after).

The whole file's wall time did not move outside the per-sample spread.
What dominates a certificate's gate is the normalizer's evaluation, and the
shape that grows it is the number of atoms (monomials are dense vectors over
all of them) times the multipliers' degree; the next lever there is filed
as [ring-certificate-kernel-cost](../issues/ring-certificate-kernel-cost.md).

## 6. Composition with `omega`

`ring` closes equations; a goal that is linear once its products are atoms
is still `omega`'s, with the products' equations stated by `ring`:

```heather
theorem mixed(a, b, c: Int, h: a * b * c <= OfNat(5)): c * (b * a) + OfNat(1) <= OfNat(6) {
    let same: (c * (b * a) = a * b * c) = ring;
    omega
}
```

`omega` was not changed. The issue assumed omega's atom table could be
reused for ring atoms; the ring reifier has its own, because the two
disagree about what an atom is (to omega a product of two variables is an
atom, to `ring` it is a monomial) and because
[omega-unfolds-defined-propositions](../issues/omega-unfolds-defined-propositions.md)
is changing omega's reflection now. Reading `ring`-normalized products as
omega atoms is a later integration, not a prerequisite.

## 7. Not in this round

- **Inequalities.** A `ring` that proves `lhs ≤ rhs` from `rhs − lhs`
  normalizing to a sum of nonnegative terms, or a `linarith`/`nlinarith` over
  ring-normalized atoms: [ring-inequalities](../issues/ring-inequalities.md).
  The regular-Cauchy estimates the reals need are inequalities, so this is
  the next step toward them.
- **`ring` modulo a setoid.** A goal `x * (y + z) ≈ x * y + x * z` at `Rat`
  is proved here through its cross-multiplication, which is the
  representation. Normalizing at `Rat` itself, modulo `≈`, needs the
  normalizer over a commutative-ring structure indexed by a relation, which is
  [semiring-ring-structure-api](../issues/semiring-ring-structure-api.md)'s
  interface plus `Respects2`; noted there.
- **Powers, `Nat` subtraction, `OfNat(x + y)` inside an `Int` goal, mixed
  `Nat`/`Int` hypotheses, rational multipliers.** Each is an atom or a
  refusal today; none has a client yet.
