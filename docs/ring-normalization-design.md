# `ring`: commutative-ring normalization by reflection

Date: 2026-10-12. Owner: [ring-normalization](../issues/ring-normalization.md).
The client that asked for it is the rationals round
([setoid-rationals-round](setoid-rationals-round.md), "Where the proof text
went"): a third of `lib/std/num/rat.hthr` was monomial rearrangement.

- [`lib/std/tactic/ring.hthr`](../lib/std/tactic/ring.hthr): the syntax, the normalizer and
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

Measured with `scripts/perf ab --source-patch` over `lib/std/num/rat.hthr`, cold
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
omega atoms is a later integration, not a prerequisite. It was built
(2026-10-28) as `linarith` at `Int` and `Nat`
([linarith-design](linarith-design.md) §8): the tactic writes these lets.

## 7. Not in this round

- **Inequalities.** A `ring` that proves `lhs ≤ rhs` from `rhs − lhs`
  normalizing to a sum of nonnegative terms, or a `linarith`/`nlinarith` over
  ring-normalized atoms: [ring-inequalities](../issues/ring-inequalities.md).
  The regular-Cauchy estimates the reals need are inequalities, so this is
  the next step toward them.
- **`ring` modulo a setoid.** Built later: §8.
- **Powers, `Nat` subtraction, `OfNat(x + y)` inside an `Int` goal, mixed
  `Nat`/`Int` hypotheses, rational multipliers.** Each is an atom or a
  refusal today; none has a client yet.

## 8. Modulo a relation

Added 2026-10-27 by [ring-modulo-a-relation](../issues/ring-modulo-a-relation.md).
A `≈` goal at a carrier with a `CommRingOfInt` instance — `Rat` and `CReal`
today — is normalized at that carrier:

```heather
theorem square(x, y: Rat): (x + y) * (x + y) ≈ x * x + 2 * x * y + y * y { ring }
theorem respects(x, x2, y: CReal, h: x ≈ x2): x * y + y ≈ (x2 + 1) * y { ring(h) }
```

**The interface.** `CommRingOfInt<A>(≈, +, *)` (lib/std/algebra/semiring.hthr)
is `CommRing` plus `of_int: Int → A` with the ring homomorphism's four laws
(zero, one, sum, product). Every commutative ring has the integers in it; the
embedding is a field so that a carrier keeps its own (`Rat::ofInt`, a rational
numeral embedded at `CReal`), which is what makes a coefficient read back as
the carrier's numeral, as `of_nat` does in `OrderedField`.

**The library.** The syntax, the normal form, `norm` and the comparison
lemmas are the `Int` path's, unchanged: coefficients are still `Int` and the
certificate's `refl` is the same evaluation. What is restated in a
`section<A: CommRingOfInt(≈, +, *)>` is the meaning — `RingExpr::eval_rel`,
`RingPoly::eval_rel` — and the soundness proof, over the ring's layers:
`rel_cong` through the `+`/`*` `Respects2` the layers carry, `inv_respects`,
`CommMonoidRel::interchange` for the rearrangements, `GroupRel::inv_unique`
for negation, and `of_int`'s laws for the coefficient arithmetic (negation is
derived from them, `of_int_neg`). Subtraction evaluates as `a + A.inv(b)`,
which is what `Rat::sub` and `CReal::sub` unfold to, so the certificate's
`eval_rel` converts to the goal's spelling. The certificate is

```text
ring::RingExpr::sound_rel<C>(__ring_atoms, ⟦lhs⟧, ⟦rhs⟧, refl)
ring::RingExpr::sound_with_rel<C>(__ring_atoms, ⟦lhs⟧, ⟦rhs⟧, D, HD, refl)
```

with the carrier written: the generic lemmas take only the atom list and
syntax, and an expected type `x ≈ y` pins the relation but not the
operations, so the carrier fixes the ring through its designations.

**The tactic.** A goal is read this way when it is the designated `≈` at its
carrier, the carrier has a `CommRingOfInt` instance in scope, and every
hypothesis is the same carrier's `≈`. The operations are the carrier's
designations (`+`, `*`, infix and prefix `-`); anything else is an atom,
compared as at `Int`; a field read is not looked through, since a value of
the carrier is not a computation the normal form wants. A numeral is the
integer its spelling ends in, confirmed by converting the term to what
`RConst` of that integer evaluates to, so a term that only spells like one is
an atom. The multiplier search is the `Int` one: hypotheses are combined with
integer polynomial multipliers, which is valid in any commutative ring.

**The fallback.** When this reading fails and the goal's `≈` unfolds to an
`Int` equation (`Rat`, not `CReal`), the cross-multiplied reading of §1 is
tried, and its certificate is used if it succeeds; if both fail the error is
the relation reading's, which is stated in the goal's terms. So the rational
laws proved with facts about the representation (`ring(hx, hy,
x.den_add(y), …)`) are unchanged, and so are the laws stated before the
`CommRingOfInt<Rat>` instance, which is registered right after `CommRing<Rat>`:
`Rat`'s own ring laws cannot be proved by a normalizer that assumes them.

**Cost shape.** The atoms are the carrier's values, not their numerators and
denominators, so a certificate's normalization runs over fewer atoms and
lower degree than the cross-multiplied one for the same identity; the
conversion that reads `eval_rel` back unfolds the instance dictionary's
projections once per operation node. The `Int` and `Nat` certificates are
unchanged.


## 9. Clearing denominators

Added 2026-10-27 by [field-simp](../issues/field-simp.md). At a `≈` carrier
`ring` proves identities of fields, not only of rings:

```heather
theorem halves(x: Rat): x * Rat::inv_succ(1) + x * Rat::inv_succ(1) ≈ x { ring }
theorem sum(x, y: CReal, hx: x.Apart(0), hy: y.Apart(0), hxy: (x * y).Apart(0)):
    x⁻¹ + y⁻¹ ≈ (x + y) * (x * y)⁻¹
{ ring }
theorem half_at(n: Nat): Rat::inv_succ(n + n + 1) + Rat::inv_succ(n + n + 1) ≈ Rat::inv_succ(n) { ring }
```

The issue asked for a `field_simp` step in front of `ring`. It is not a
separate step: clearing is part of how `ring` reads a field goal, so there is
no new surface and nothing to chain.

**A reciprocal is an atom with a fact.** `x⁻¹` (the carrier's designated
postfix `⁻¹`) is an atom `r`, read together with the lemma that sits beside
the operation, `<op>_mul`: `x⁻¹ * x ≈ 1` (`Rat::inv_mul`, `CReal::inv_mul`).
`Rat::inv_succ(n)` is read with `Rat::inv_succ_cancel`:
`inv_succ(n) * (Rat::ofInt(OfNat(n)) + 1) ≈ 1`. Each fact is a polynomial
`r·d − 1 = 0`, and the certificate cites it the way it cites a written
hypothesis (`sound_with_rel`, `hyp_rel`), so the soundness proof of §8 is all
there is. Apartness is the one `x⁻¹` was elaborated with (its `h := infer`
found it when the goal was written), so clearing owes no side condition; the
issue's "discharge from `Pos` binders, numerals and hypotheses" is the
evidence search that already ran. A reciprocal whose fact cannot be written
stays a plain atom.

**The multipliers are computed, not searched for.** With `H = r·d − 1` and
`P = Σ pₐ·rᵃ` (the `pₐ` free of `r`, `K` the top power):

```text
dᴷ·P = Σ pₐ·dᴷ⁻ᵃ·(rd)ᵃ = P′ + H·M      P′ = Σ pₐ·dᴷ⁻ᵃ,  M = Σ pₐ·dᴷ⁻ᵃ·Sₐ,  Sₐ = Σ_{t<a} (rd)ᵗ
P = rᴷ·P′ + H·(rᴷ·M − S_K·P)
```

so `P` is a combination of the facts exactly when the cleared `P′` is.
Eliminating every reciprocal, the last met first (a reciprocal inside
another's denominator is met first, so it is still there to eliminate when the
outer one's `d` brings it in), leaves a polynomial free of them that is zero
exactly when the goal is an identity of fields at those denominators. A true
identity is never missed, unlike §4's bounded search, and no multiplier has a
fraction. Written hypotheses are searched for against what clearing leaves,
each with the definitions below substituted the same way first (so a
hypothesis spelling `ofRat(x)` meets a goal spelling `ofRat(2 - x)`; the
substitution's multipliers are given back to the definitions' rows, and a
reciprocal in a hypothesis stays an atom there,
issues/ring-hypotheses-cast-spelling.md); failing that, every row is searched
together. The Rust side checks its own
combination before writing it.

**Casts.** `inv_succ(n + n + 1)`'s denominator is `Rat::ofInt(OfNat(n + n +
1))`, which no ring identity relates to `ofInt(OfNat(n))`. A cast of a `Nat`
sum, product or successor is therefore an atom `c` read with a definition
`c ≈ e` that pushes the embedding one level in — `RingExpr::of_nat_add`,
`of_nat_mul`, `of_nat_succ`, stated once in the `CommRingOfInt` section of
`ring.hthr` — and `e`'s casts are read the same way down to atoms and
numerals. A definition is eliminated by substitution
(`cᵃ − eᵃ = (c − e)·Σ_{t<a} cᵗ·eᵃ⁻¹⁻ᵗ`). A cast is recognized by its spelling,
`…OfNat(e)…` with only closing parentheses after it, and confirmed by
converting the atom to the lemma's left side (`of_int` at the same `e`), so
the same reading serves `CReal::ofRat(Rat::ofInt(OfNat(e)))`.

**Refusals.** A goal that is not an identity is named by what clearing leaves,
with both it and the product of the denominators divided by the largest
monomial they share: `x⁻¹ + y⁻¹ ≈ (x * y)⁻¹` reports that, multiplied by
`x * y`, the sides differ by `y + x - 1`. The product is the denominators'
product, not their least common multiple; only the message would change.

**Where it is used.** `CReal`'s regularity proofs carried calc chains of
`inv_succ_half` and `add_respects` / `add_add_add_comm` rearrangements; five
of them are now one `ring` step each. `Rat::inv_succ_mul` and
`Rat::inv_succ_half` themselves are now `ring`'s too
(`lib/_tests/std/tactic/ring_field_tests.hthr`), though they keep their proofs:
they are stated before `CommRingOfInt<Rat>`.

**Not in this round.**

- The inequality form (positive denominators preserve `≤`), the consumer
  being [linarith-ordered-fields](../issues/linarith-ordered-fields.md).
- Reciprocals at a generic `OrderedField` (`A.recip(x, h)`): the relation
  reading needs a concrete carrier with a `CommRingOfInt` instance.
- `Rat::recip` (total) and `x ^ n`: atoms. The first needs a searched
  apartness to state its fact; the second a power reading.
- A field read such as `x.seq(n)` inside the goal did not spell as source,
  which refused the whole reading; the `CReal` proofs above apply `ring`
  under `add_respects` for that reason. Since `linarith`'s round such an
  atom is named in the atom list by an alias bound to its term
  (docs/linarith-design.md §4).
