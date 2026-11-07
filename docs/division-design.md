# Division: `a / b` at a searched nonzero divisor

Status: landed at `Rat` and `CReal` (issues/rat-division-symbol.md) and over
the ordered-field classes (issues/ordered-field-division-symbol.md, §6).
Builds on docs/inverse-power-notation-design.md, whose decision this extends.

## 1. The decision

`/` at a field means what `⁻¹` already means: no junk value. `a / b` is
`a.div(b, h)` with `h: b.Apart(0) := infer`, and its value is `a * b⁻¹` at
the same proof, so

```heather
theorem Rat::div_eq_mul_inv(self a, b: Rat, h: b.Apart(0) := infer): a / b = a * b⁻¹ { refl }
```

The alternative the issue weighed, Lean's total `a / 0 = 0`, would have made
`/` and `⁻¹` disagree about 0 (the total reciprocal `Rat::recip` is not the
notation), and every field law would have carried `b ≠ 0` anyway. Minus
chose the proof (2026-11-06), on the condition that the proof is found
wherever it reasonably can be. Most of this round is that condition.

`Nat`, `Int`, `BitVec(n)` and `SInt(n)` keep their total `/`
(issues/integer-operator-symbols.md): truncating or Euclidean division is the
operation there, not a field inverse, and `n / 0` has its conventional value.

## 2. Where the proof comes from

The search is `:= infer`'s (docs/facts-on-demand-design.md §2), at the goal
`b.Apart(0)`. In order:

1. **Locals, up to conversion.** `b.Apart(0)`, `0 < b`, `b < 0`, and at
   `Rat` also `¬(b ≈ 0)`. The last three reach `Apart` through one-place
   predicates (`Positive`, `Negative`, `Nonzero`) that a local converts to,
   because a rule from `0 < b` to `b.Apart(0)` would fail Paterson's
   condition (§3).
2. **Computation.** A closed divisor's sign evaluates: `1 / 2`, `a / (3 - 1)`,
   `a / (-3)`.
3. **Sign rules**, recursively. `Positive` and `Negative` through `+`, `*`,
   `/`, `⁻¹`, `npow`, `^` and prefix `-`; `NonNeg` through `+`, `*`, `x * x`,
   `x ^ 2` and `abs`; a positive plus a nonnegative is positive. So
   `a / (b ^ 2 + 1)`, `a / (b.abs() + 1)` and `a / (b⁻¹ + 1)` at `0 < b`
   need nothing written. At the rules' leaves, a sum or difference no rule
   signs is `nlinarith`'s (`positive_add_by_nlinarith`, `…_sub_…`, and the
   negative pair: search rules keyed by `+`/`-`, so a local never runs
   them), and a nonnegative is `linarith`'s (`nonneg_by_linarith`, which
   reads a positive local): `a / ((c - b) + e.abs())` at `b < c`. `apart_mul`, `apart_inv`, `apart_div` carry
   apartness itself through products, inverses and quotients of numbers
   whose sign is unknown.
4. **`nlinarith`, last.** Two search rules (§3 of the facts-on-demand note),

   ```heather
   evidence theorem Rat::apart_by_nlinarith({x: Rat}, h: 0 < x := nlinarith): x.Apart(0) { Inr(h) }
   evidence theorem Rat::apart_by_nlinarith_neg({x: Rat}, h: x < 0 := nlinarith): x.Apart(0) { Inl(h) }
   ```

   run only after every plain rule about `Apart` failed, so a divisor that a
   local or a rule answers never pays for them. They read the caller's
   hypotheses: `a / (c - b)` at `b < c`, `a / (b * c - 1)` at `1 < b`,
   `1 < c`, `a / (1 + b * b)`. The positive side is tried first (its name
   sorts first), since positive divisors are the common case.

Refused: a divisor nothing is known about, `0`, and `b` at `¬(b = 0)`.
The last is deliberate: `=` at `Rat` is the pair's equality and `Rat(0, 2)`
is not `Rat(0, 1)`, so `¬(b = 0)` does not give `¬(b ≈ 0)`.

**At `CReal`** the same, except no rule from `¬(b ≈ 0)` (constructively it
does not say which side of zero `b` is on, so it gives no apartness), and
`nlinarith` proves `<` only by a direct combination, since a refutation of
`b <= 0` is not a proof of `0 < b` there. `positive_ofRat`/`negative_ofRat`
give an embedded rational its sign, so numerals are found.

## 3. Why the rules have this shape

- **One-place predicates.** Paterson's condition wants a `:= infer`
  premise smaller than the conclusion. `x.Positive()` is smaller than
  `x.Apart(0)`; `0 < x` is not. The same reason gives `Nonzero` and
  `NonNeg`.
- **No `Positive ⇒ NonNeg` rule.** Its premise would be the same size as its
  conclusion. A positive plus a positive therefore has its own rule
  (`positive_add`) beside `positive_add_nonneg` and `positive_nonneg_add`,
  and `nonneg_by_linarith` (a search rule, not measured) reads a positive
  local as nonnegative.
- **Written sign goals.** `lt_of_positive`, `lt_of_negative`, `le_of_nonneg`
  go the other way, from the one-place predicate to `0 < x`; that direction
  passes Paterson's condition, so a goal `0 < a / b` (`positivity`, a
  `h: 0 < e := infer` parameter) reaches every sign rule.
- **No search rule inside an arithmetic tactic.** While `linarith`, `ring`
  or `omega` reads or checks (`ring_depth`/`omega_depth` above zero), the
  search skips search rules: their tactics would start nested runs whose
  reading meets the same goals (a reciprocal's apartness in a context
  `nlinarith` reads), bounded only by the depth cap. Without the guard
  `rat_den_sum` in the `linarith` probes ran past its CPU rail.
- **Arithmetic only at `Apart`.** Putting the `nlinarith` search rule at
  `Positive`/`Negative` instead would let it reach the leaves of the sign
  rules, but every successful `x⁻¹` at a positive local would first fail
  a `Negative` search, and so pay a failing `nlinarith`
  (`apart_of_negative` sorts before `apart_of_positive`). At `Apart`, search
  rules come after all plain rules, so the common case is unchanged.

## 4. The tactics read `/` and `^`

- **`ring`** reads `a / b` as `a * b⁻¹` at the same proof (`Reifier::quotient`
  in `crates/elab/src/ring.rs`): the reciprocal is written out, elaborated,
  and read as every `x⁻¹` is, with its fact `x⁻¹ * x ≈ 1`, so field identities
  with quotients are `ring`'s (`a / c + b / c ≈ (a + b) / c`,
  `a / 4 + a / 4 ≈ a / 2`). The certificate's kernel check unfolds `/` once.
- **`ring`** reads `x ^ n` at a literal exponent as the product `npow`
  computes, `1 * x * … * x` (up to `MAX_POWER`), and at a negative literal
  as that power of `x⁻¹` at the power's proof (`Reifier::literal_power`), so
  `(a + b) ^ 2 ≈ a ^ 2 + 2 * a * b + b ^ 2` and `b ^ (-2) * b ^ 2 ≈ 1` are
  `ring`'s, and `nlinarith` sees `x ^ 2` as the square it is.
- **`linarith`** clears a reciprocal whose denominator some fact shows
  positive. A numeral denominator has no such fact in scope, so the reading
  now builds `0 < d⁻¹` for a positive numeral `d` from the carrier's
  `positive_inv` rule (`FieldReading::numeral_reciprocal_positive`): `a / 2 < a`
  at `0 < a`, and the midpoint `a < (a + b) / 2 < b`, are `linarith`. Only
  numerals: a neutral denominator's positivity is a fact the rows hold or not,
  and a search per reciprocal would be paid by every reading.

## 5. Library

At `Rat`: `div`, `div_eq_mul_inv`, `div_any_proof`, `div_mul_cancel`,
`mul_div_cancel`, `div_self`, `div_one`, `one_div`, `zero_div`,
`div_respects`, `add_div`, `sub_div`, `mul_div_assoc`, `inv_mul_distrib`,
`div_mul_div`, and the rules of §2. At `CReal`: `div`, `div_eq_mul_inv`,
`div_mul_cancel`, `mul_div_cancel`, `div_self`, `one_div`, `div_respects`,
`add_div`, `mul_div_assoc`, the sign rules, `apart_mul`, `apart_inv`,
`apart_div`. Probes: `lib/_tests/std/num/{rat,creal}_tests.hthr`,
`lib/_tests/std/tactic/{ring_field,linarith}_tests.hthr`.

## 6. Over the ordered-field classes

`lib/std/algebra/field_division.hthr` states the same once, inside
`section<A: OrderedField(≈, <, <=, +, *)>`:

```heather
fn OrderedField::Invertible(self x: A) → Type { ApartBy(<, x, A.unit) }
fn OrderedField::inv(self x: A, h: x.Invertible() := infer) → A { A.recip(x, h) }
fn OrderedField::div(self a, b: A, h: b.Invertible() := infer) → A { a * A.recip(b, h) }
designation postfix ⁻¹ at OrderedField := OrderedField::inv
designation / at OrderedField := OrderedField::div
```

- **A designation at a class.** A section's operand at its type parameter
  `K` has no nominal carrier, so rung 2 of the operator ladder
  (docs/operators-onto-classes-design.md §4) finds nothing. Rung 2b then
  takes the designation at the class of a dictionary in scope, innermost
  first (`designated_at_scope_class` in `crates/elab/src/dispatch/operator.rs`).
  The operation is emitted bare, as every designated one is, so its own
  dictionary is resolved at the operand's carrier. A carrier's own
  designation always wins: `Rat` keeps `Rat::div`.
- **Rules in a class section.** An evidence rule stated in the section has
  the section's dictionary as a premise. It is a class goal, which the
  instance registry answers under its own decrease check, so it is exempt
  from Paterson's condition (`register_evidence`). The rule's operations
  are its own binders, so `positive_mul`'s `x * y` would unify with a goal's
  `c + d`. A first-order pre-match (`rule_clashes`) skips a rule whose binder
  would have to be two different locals, or whose applied binder meets a
  bare local; anything it cannot read, it leaves to the trial.
- **Sign predicates generic in the relation.** `PositiveBy(lt, le, zero,
  x)`, `NegativeBy`, `NonNegBy`, like `ApartBy`. The relation is a local in
  a section, and a rule needs a global head to be keyed. Both relations are
  arguments so that a nonnegative premise mentions nothing its positive
  conclusion does not. `Invertible(x)` carries the section's whole index,
  so a sign premise is smaller than it.
- **Rules at the weakest class.** The predicates and the rules for `+`,
  negation and `*` are `lib/std/algebra/ordered_sign.hthr`'s, each in a
  section over the weakest class whose laws prove it: `OrderedAddMonoid`
  (`positive_add`, `negative_add`), `LocatedAddMonoid` (a sum with a
  nonnegative summand), `OrderedAddGroup` (negation), `OrderedSemiring`
  (`positive_mul`, `nonneg_mul`, `positive_one`) and `OrderedRing` (a
  negative factor, `nonneg_mul_self`). Only the rules for `⁻¹` and `/`, the
  apartness rules and the arithmetic fallbacks are at `OrderedField`. Used
  in a field section, a weaker rule's dictionary premise is an upcast; the
  first round stated every rule at the field because that upcast was built
  as a record at every application (about twenty times a field rule's
  cost). Open derivations (docs/traits-layer2-design.md §8.1) mint it once
  per context prefix, after which it is an application, so the rules moved
  down (issues/sign-rules-at-weakest-class.md). The same search now answers
  a sign goal in any ordered semiring or ring section, and at `Nat` and
  `Int` through their instances. Two resolver changes came with the move.
  A rule is cited by its key on the caller's behalf, so its module need
  only be in the caller's import closure: a client of `field_division`
  imports `ordered_sign` through it (`rule_citation`, `Names::reaches`);
  before, every moved rule failed to build there and the `nlinarith`
  fallbacks answered instead. And rules over a class are tried weakest
  class first, then in canonical order (`rule_class_rank`): canonical order
  put `LocatedAddMonoid::positive_add_nonneg` before
  `OrderedAddMonoid::positive_add`, and its nonnegative premise ran
  `linarith` where `positive_add` needed nothing. A second pass that
  withholds every search rule first was tried and dropped: a goal plain
  rules cannot answer then paid for its plain search twice.
- **Arithmetic last.** `invertible_by_nlinarith`/`_neg` and, at the leaves,
  `positive_add_by_nlinarith`, `negative_add_by_nlinarith` (subtraction is
  `x + K.inv(y)` there) and `nonneg_by_linarith`. A tactic default runs in a
  context with the caller's locals renamed out of reach; it now keeps the
  dictionaries over type parameters and the symbols their constraints
  installed (`Cx::hygienic`), which `linarith` needs to spell `K.unit`.
  `invertible_above_zero` sorts before `invertible_below_zero`, so a positive
  divisor does not first pay a failing `nlinarith`.
- **Tactics.** `ring` and `linarith` read `OrderedField::inv` and `div` at a
  class carrier as at `Rat` (`class_carrier` in `crates/elab/src/ring.rs`).

A carrier reads the generic laws through its instance by unfolding:
`OrderedField::div_mul_cancel(a, b, h := Inr(hb))` proves `a / b * b ≈ a` at
`Rat`. The carriers' own copies stay (issues/carrier-division-through-class.md).
Probes: `lib/_tests/std/algebra/field_division_tests.hthr`, and below the
field `lib/_tests/std/algebra/ordered_sign_tests.hthr`.

## 7. Left open

The first round left four gaps that the second closed
(apart-search-arith-leaves, sign-goal-views, ring-reads-integer-powers,
search-trace-goal-display; a failed search's trace now spells each goal it
tried). Still open:

- issues/all-numeral-relations-default-to-nat.md: `1 / 2` with no expected
  carrier is `Nat` division, `0`.
- issues/carrier-division-through-class.md: `Rat`'s and `CReal`'s `/` as
  the class's, retiring their copies.
- issues/class-carrier-division-gaps.md: a sign goal written with `<` at a
  class carrier, numerals there, and the trace's spelling.
- issues/ring-reciprocal-of-searched-proof.md: `ring` reads no fact for a
  reciprocal whose apartness the search built through a rule.
