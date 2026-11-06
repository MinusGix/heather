# Inverse and power notation: `x⁻¹` and `x ^ n`

Status: landed with `Rat` and `CReal` as the carriers.

## 1. The decision: a searched hypothesis, not a junk value

Lean writes `x⁻¹` and `x ^ n` and makes `x⁻¹` total: in a field `0⁻¹ = 0`,
and `x ^ (-1) = x⁻¹` holds because `zpow` at a negative exponent is defined
through `⁻¹`. The price is the junk value. Every law about `⁻¹` that is false
at 0 (`x * x⁻¹ = 1`) carries a `x ≠ 0` premise anyway, so the hypothesis is
still paid, only later, and a statement that forgets it is true and
misleading rather than refused.

Heather keeps the hypothesis at the value. `x⁻¹` is `x.inv(h)` with
`h: x.Apart(0) := infer`, a defaulted parameter that the search fills at the
call (docs/positivity-evidence-design.md, docs/named-arguments-design.md
§9.6). So the hypothesis is free wherever it is evident:

- a local apartness, or a local sign (`0 < x`, `x < 0`) by conversion;
- a product, inverse or power of such things, by evidence rules;
- a literal, by computation (`2⁻¹`, `(-3)⁻¹`).

Where none of those holds, `x⁻¹` is refused, and `0⁻¹` has no meaning to
leak. The reals need apartness anyway (an inverse there must read a gap from
zero), so the rationals use the same hypothesis and the two carriers state
their field laws the same way. At `Rat` apartness and `¬(x ≈ 0)` are
interchangeable (`Rat::apart_of_nonzero`, `Rat::nonzero_of_apart`); at
`CReal` they are not, and apartness is the one that computes.

The total reciprocal survives under its own name, `Rat::recip` (0 goes to
0). It is the raw arithmetic `inv` computes and that a real's inverse reads
term by term, never the notation.

## 2. Syntax

- `x⁻¹` is a **postfix** operator. It binds like `.f` and `(args)`, so
  `x⁻¹.f`, `x⁻¹⁻¹` and `f(x)⁻¹` read as written. The lexer takes `⁻¹` as one
  token (superscript minus, superscript one).
- `a ^ b` sits **above prefix negation and below postfix**, and associates
  to the right: `-x ^ 2` is `-(x ^ 2)`, `a ^ b ^ c` is `a ^ (b ^ c)`, and
  `x⁻¹ ^ 2` is `(x⁻¹) ^ 2`. The exponent is a prefix expression, so
  `x ^ -1` parses without parentheses. This is the conventional reading and
  Lean's.
- Both are designations: `designation postfix ⁻¹ at Rat := Rat::inv` and
  `designation ^ at Rat := Rat::pow`. `postfix` joins `prefix` as a fixity;
  `⁻¹` is the only postfix symbol.
- The formatter hugs `⁻¹` to its operand and spaces `^` like any infix.

## 3. The library shape

At each carrier (`lib/std/num/rat.hthr`, `lib/std/num/creal.hthr`):

- `Apart(x, y)` is `x < y ∨ y < x`, with `apart_sym` and `apart_irrefl`.
- `Positive` / `Negative` are one-place sign predicates, the premises of the
  rules `apart_of_positive` / `apart_of_negative`. A rule from `0 < x` to
  `x.Apart(0)` would not pass the termination check (the premise is no
  smaller than the conclusion); `x.Positive()` is smaller, and a local
  `0 < x` is one by conversion.
- `inv(self x, h: x.Apart(0) := infer)`, the inverse. `inv_any_proof`: the
  value does not depend on the proof (by `refl` at `Rat`, by `≈` at `CReal`,
  where different gaps read different indices).
- `npow(x, n: Nat)`, total, with `npow_add`, `npow_respects` and at `Rat`
  `mul_npow` and `one_npow`.
- `PowOk(x, n: Int)` is `True` at `OfNat(_)` and `x.Apart(0)` at
  `NegSucc(_)`, and `pow(self x, n: Int, h: x.PowOk(n) := infer)` is `npow`
  at a natural exponent and `npow` of the inverse at a negative one. So
  `x ^ 2` asks for nothing, `x ^ (-1)` asks exactly what `x⁻¹` asks, and a
  neutral exponent asks for a proof the caller must supply.
- The unification the issue asked for: `pow_neg_one: x ^ (-1) ≈ x⁻¹`, and
  more generally `pow_negSucc_inv: x ^ NegSucc(k) ≈ (x ^ Succ(k))⁻¹`, with
  `pow_zero`, `pow_one`, `pow_two`, `pow_ofNat`, `pow_negSucc`. These are
  `≈` rather than `=` because `npow(x, 1)` is `1 * x`.

Rules for the search at `Rat`: `apart_mul`, `apart_inv`, `apart_npow`,
`apart_pow`. At `CReal`: the sign rules and `ofRat_apart` (an embedded
rational is apart from zero when the rational is). There is no `apart_mul`
at `CReal` yet: products against the order are `issues/creal-mul-order.md`.

## 4. Two search changes

**A goal headed by a definition no rule is about is unfolded.** The goal
`x.PowOk(-1)` names `PowOk`, which no rule concludes. Before reporting
`no-rule`, the search takes the goal's reducts (a bounded number of steps)
and stops at the first whose head relation differs; if some rule is about
that relation (`Apart`), it searches that goal instead. The bound is small
because the definitions this serves compute in a handful of steps; a goal
still stuck past it is answered as before. A goal headed by a relation that
has rules is never unfolded, so existing searches are unchanged.

**A record or sum value written out has a head in the prefilter.** The rule
prefilter compares argument heads and treated anything but a global
application or a Nat constructor as a wildcard. A literal `Rat(OfNat(2), 1)`
is a pair, so every rule about `Apart` (products, powers, inverses) passed
the filter and was tried with metavariables, recursively. Pairs, `Inl` and
`Inr` now have heads of their own, which no global application shares
without unfolding, which the prefilter never does. This is what keeps
`CReal::ofRat(Rat(OfNat(2), 1))⁻¹` as cheap as an explicit proof.

## 5. What clients need

- `-1` and `2` at `Int` are numerals, which need `import algebra` directly.
- A defaulted parameter is passed by name: `x.inv(h := p)`, `x.pow(n, h := p)`.
- `algebra` and `algebra_rel` both declared `Semigroup` when this round
  landed, so `rat` and `creal` imported `algebra_rel::{Semigroup,
  Commutative}` by name. The relational class is now `SemigroupRel`, and both
  modules import `algebra_rel` whole (issues/rat-numerals-and-semigroup-clash.md).

## 6. Left open

- ~~`¬(x ≈ 0)` in scope does not give `x⁻¹` at `Rat`~~: since the division
  round (docs/division-design.md) `apart_of_nonzero` is a rule over a
  one-place `x.Nonzero()`, which a local `¬(x ≈ 0)` converts to.
- ~~`CReal` has no rule for products~~: it has `apart_mul`, `apart_inv` and
  `apart_div` since the same round.
- Integer-exponent laws beyond the unification (`pow_add` over `Int`,
  `(x * y) ^ n`) are not stated yet.
- A shared ordered-field interface would state `inv` and `pow` once
  (`issues/constructive-ordered-field-interface.md`).
