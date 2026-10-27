# The monotonicity tactic (`mono`)

Issue: `issues/monotonicity-tactic.md`. Code: `lib/std/tactic/mono.hthr`;
probes and refusals: `lib/_tests/std/tactic/mono_tests.hthr`; first client:
`lib/std/num/float/series.hthr`.

## 1. What it is for

Most of a real-number proof is monotonicity plumbing. Before this tactic a
bound such as `t·r + t·r <= t·h + t·h` under `|r| <= h` was written

```
Rat::add_le_mono(Rat::mul_le_mono_l(s.small(k, hk), t.abs_nonneg()), …)
```

spelling the goal's shape a second time as a tree of `*_mono` lemmas and
discharging every sign side condition by hand. `mono` reads the shape off
the goal instead:

```
<= t.abs() * h + t.abs() * h := by mono_with([s.small(k, hk)]),
```

It is Lean's `gcongr` in spirit, written as an ordinary `Tac<Expr>` in
Heather (`docs/host-elaboration-interface-design.md`): nothing about it is
trusted, and the proof it returns is a tree of calls to the carriers' own
theorems, checked at the `by` like any other term.

## 2. Surface

- `by mono()` proves `l <= r` or `l < r` at `Rat`, `CReal`, `Int` or `Nat`,
  or at a carrier with an ordered class's dictionary in scope (§8), from the
  goal's hypotheses.
- `by mono_with([e₁, …])` also uses the terms `eᵢ` (any terms of the goal's
  context, quoted as tactic arguments are) for the leaves. The list needs
  `import list` where it is written.
- `depth := n` (both forms) bounds how many goals deep it splits; the
  default is 64.

A block's `let` names are not among the goal's hypotheses as a tactic sees
them (`Goal` lists binders, and a `let` is substituted), so a fact held in a
`let` is passed with `mono_with([step])`.

`calc` steps take it as their justification with `by`: `<= … := by mono()`.

## 3. The search

At a goal `R(l, r)` with `R` the carrier's `<=` or `<`:

1. **Outright.** A given term, then a hypothesis, whose statement is the
   goal (compared by conversion, only for candidates that apply `R`).
2. **Split.** If `l` and `r` are the same global `op` applied, the tactic
   computes the argument positions where they differ: the least general
   generalization of the two sides, one layer deep, read syntactically
   (§4). It picks the carrier's first law for `op` at `R` whose movable
   positions cover the differing ones, and `apply`s it: the law's conclusion
   is matched against the goal, and its premises become goals, proved by
   the same search. The laws are listed one-sided before two-sided, so a
   goal that keeps an operand fixed owes nothing about it.
3. **Leaf.** Otherwise, in order: reflexivity (at `<=`); the sign laws for
   `r`'s head when `l` is zero (`0 <= x.abs()`, `0 <= x * y` from the signs
   of the factors, `0 < Rat::inv_succ(n)`, …); computation, when both sides
   are closed (the statement converts to `True`); and at `<=`, the same
   search at `<` through the carrier's `le_of_lt`. Each is attempted, and a
   failure lists every alternative under the goal it left open.

A law decides its own variance: `Rat::neg_le` concludes `-y <= -x` from
`x <= y`, `Rat::sub_le_sub_l` concludes `x - b <= x - a` from `a <= b`, and
`Rat::recip_le_recip` carries a positivity premise. The search does not know
which positions are antitone; matching the conclusion does that.

The tactic proves the goal or fails; it does not leave goals open. A failure
is reported at the deepest goal nothing proved, which is where the missing
fact belongs.

## 4. Comparing the two sides

`mono_same` walks both sides with `View` as a work list of pairs: two
presented heads (a global, a local, a field read, a literal) are compared by
identity (a field by its name, its record queued as argument 0) and their
arguments queued, two different presented heads are different terms,
and a pair the view does not present on one side (a `λ`, a proof argument)
is compared by conversion. This is the syntactic least general
generalization of `issues/congruence-by-anti-unification.md` §3, taken one
layer at a time because each layer is a separate law.

Syntactic comparison can call two convertible terms different. That costs a
premise `a <= a'` with `a ≡ a'`, which the leaf's reflexivity proves by
matching `le_refl`'s conclusion, i.e. by conversion. It never makes the
tactic prove something false: every proof is checked.

## 5. The laws

`mono_carriers()` lists, per carrier, the two orders, `le_refl`,
`le_of_lt`, the monotonicity laws `(strict, op, moves, lemma)` and the sign
laws `(strict, op, lemma)`, by name. They are resolved where the tactic runs
(`Lookup`), and a name that does not resolve is skipped, so a client that
imports `rat` and not `creal` resolves only what it can see. Only the
carrier whose order the goal is resolves its laws.

This round added the laws the registry wanted and `rat` lacked:
`Rat::add_nonneg`, `Rat::add_pos`, `Rat::sub_le_sub`, `Rat::npow_nonneg`,
`Rat::npow_pos`, `Rat::npow_le_mono`.

## 6. Cost

Every run pays a fixed part, which dominates small goals: building the
carrier table and resolving its laws by name, evaluated as strategy code
between requests (`issues/tactic-strategy-step-cost.md`). Past that, the
search is linear in the size of the two sides: one `View` per node per side,
one `apply` per split, and conversion only at the outright check and where
the view does not present a pair. The sign search at a leaf is bounded by
the leaf's own structure.

## 7. Not done

- **Concrete carriers through their classes.** `Rat` and `CReal` have
  `OrderedField` instances, so §8's laws would apply there too and the
  per-carrier tables could shrink to what the classes do not state (`abs`,
  `npow`, `inv_succ`). They are kept: a class law at a concrete carrier
  needs its dictionary by instance resolution and, for an ancestor's law, an
  upcast record in the proof term, a cost per law where the carrier's own
  theorem has none, and a concrete goal's operations are globals the class's
  index would have to be matched against through the designations
  (`operators-onto-classes-design.md`).
- **Without `by`.** The issue sketched `:= mono(h)` as a calc
  justification; a tactic runs under `by`, so it is `:= by mono_with([h])`.
- **More laws.** `CReal` has no `npow` monotonicity or `abs_nonneg` yet,
  `Int` no strict addition laws; each is a line in the table once the
  theorem exists. At a class carrier, an `OrderedAddGroup` without
  locatedness has no strict translation on the right as a theorem (the
  class's own `add_lt_mono_r` is a field, and a theorem of that name would
  make every `A.add_lt_mono_r` ambiguous), and `recip` has its sign law but
  no monotonicity row (`recip_lt_recip` takes apartness proofs).
- **One law per split.** The first law whose positions cover the differing
  ones is the one applied; `a + c < b + d` from `a <= b` and `c < d` needs
  `add_le_lt_mono` where the table's first two-sided strict law is
  `add_lt_le_mono`, and fails. Trying the next law after a failed one would
  cost a failure's worth of search per law.

## 8. Class carriers

Issue: `issues/mono-class-laws.md`. Inside `section<A: OrderedField(≈, <,
<=, +, *)>` a goal `z + x <= z + y` is the section's local `<=` applied to
the local `+`'s applications: the class's index operations are binders of the
section, and `View` presents them as `HLocal`. Fields of the dictionary are
not binders: `A.inv(x)` and `A.unit` are projections out of the dictionary
local, which `View` presents as `HField(record, name, args)`
(`docs/host-elaboration-interface-design.md` §18).

- **The carrier.** A goal whose relation is not a concrete carrier's order
  is read off the context: the first local whose type views as one of
  `mono_classes`' classes (`OrderedField`, `LocatedAddGroup`,
  `OrderedAddGroup`, `PseudoOrder`, `StrictOrder`, strongest first), and
  whose `<=` or `<` argument is the goal's relation. The class's laws name
  their operations by the dictionary's argument positions (`+` is argument 4
  of `OrderedField<A>(≈, <, <=, +, *)`) or by field (`inv`, `recip`), and are
  keyed by what those are at this dictionary: the comparison of two sides'
  operations is over a key that is a global, a local or a field name.
- **The laws.** They are the classes' theorems, stated once, by the weakest
  class that proves them (`OrderedAddGroup::add_le_mono_l`,
  `LocatedAddGroup::neg_le`, `OrderedField::mul_le_mono_l`), and a class's
  table is its ancestors' rows and its own. `apply` uses them unchanged:
  `Match` fills a class lemma's dictionary and the indices its conclusion
  does not mention from the dictionary in scope, upcast where the lemma's
  class is an ancestor's (`host-elaboration-interface-design.md` §18). A
  field read's record is its argument 0, so `A.inv(x)` moves at position 1.
- **What the classes lacked.** `≤` monotonicity of a product needs a
  nonnegative factor, and the class has only `pos_of_mul_pos` at a positive
  one: `OrderedField::pos_of_mul_pos_nonneg` places a nonnegative `z` with
  `0 < z·d` by cotransitivity (either `(z + 1)·d` is positive too, or `d` is
  negative and `z·(-d) < 0` puts `z` below zero), and `mul_le_mono_l/r`,
  `mul_nonneg` and `mul_le_mul` follow. Sums got their sign laws and the mixed
  strict/weak sums; `mul_pos_of_pos` is the field `mul_pos` under a name a
  lookup can use.

Reflexivity and weakening are `StrictOrder::le_refl` and `le_of_lt` at every
class. Computation never closes a class goal (a dictionary is not closed), so
that leaf alternative fails at once.
