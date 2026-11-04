# `norm_num`: closed numeric facts by evaluation

Date: 2026-10-27. Owner: [numeral-normalisation](../issues/numeral-normalisation.md).

- [`lib/std/tactic/norm_num.hthr`](../lib/std/tactic/norm_num.hthr): the
  tactic, `norm_num()`, and the step other tactics call, `norm_num_at(t)`.
- [`lib/std/tactic/norm_num_real.hthr`](../lib/std/tactic/norm_num_real.hthr):
  the `NumReal` tree at `CReal` and its soundness.
- The verdicts and their soundness lemmas live with their types:
  `Nat::le_of_leb`, `not_le_of_leb`, `ne_of_same` (`nat.hthr`);
  `Int::same`, `leb` and their lemmas (`int.hthr`); `Rat::same_bool`,
  `le_bool`, `lt_bool` and theirs (`rat.hthr`); the embedding laws `CReal`
  lacked (`ofRat_sub`, `ofRat_npow`, `ofRat_abs`, `apart_respects`,
  `not_same_of_apart`, in `creal.hthr`).
- Probes: `lib/_tests/std/tactic/norm_num_tests.hthr` and
  `norm_num_real_tests.hthr`, refusals included.

## 1. What a client writes

```heather
import norm_num;

theorem a(): Nat::pow(2, 64) * Nat::pow(2, 64) = Nat::pow(2, 128) { by norm_num() }
theorem b(): Rat::inv_succ(1) + Rat::inv_succ(1) ≈ 1 { by norm_num() }
theorem c(): Rat(355, 113) < 4 { by norm_num() }
theorem d(): ¬(Rat(1, 3) ≈ Rat(33, 100)) { by norm_num() }
theorem e(): Dyadic(1, -1) + Dyadic(1, -2) < 1 { by norm_num() }

import norm_num_real;   // for goals at `CReal`
theorem f(): third() + third() + third() ≈ 1 { by norm_num() }
theorem g(): CReal::ofRat(2) ^ (-2) ≈ CReal::ofRat(Rat(1, 4)) { by norm_num() }
```

The goal is `=`, `≈`, `<`, `<=` or `Apart` between two closed numeric
expressions, or the negation of one (`≠`, `¬(x < y)`, `¬(x.Apart(y))`), at
`Nat`, `Int`, `Rat`, `Dyadic`, `Finite(F)` or `CReal`. `=` is read at `Nat`
and `Int` only: at the other carriers it is representation identity (`1/2`
and `2/4` differ), and the tactic says to state `≈`.

## 2. Two proof routes, neither a conversion over the numbers

**Carriers that compute: a `Bool` verdict.** At `Nat`, `Int` and `Rat` the
relation is decidable by computation, so the proof is a verdict proved
`= True` (or `= False`, for a negation) and a lemma turning it into the
fact: `Nat::le_of_leb(n, m, h: n.leb(m) = True): n <= m`,
`Rat::same_of_bool(x, y, h: x.same_bool(y) = True): x ≈ y`, and so on.
`Int`'s verdicts are `Nat`'s `same` and `leb` by cases on the signs, and
`Rat`'s are `Int`'s over the cross products, which is what `Rat::Same`,
`Le` and `Lt` are. `Lt` at `Int` and `Rat` is `a.isucc() <= b`, so its
verdict is that `leb`. `Dyadic` and the floats need nothing of their own:
their relations are `Rat`'s of their value by definition (`Dyadic::Lt(a, b)`
is `a.rat() < b.rat()`, `Finite::Lt(x, y)` is `x.dyadic() < y.dyadic()`),
so the tactic decides `Rat`'s relation of `Dyadic::rat(l)` or
`Finite::val(l)`, and the lemma's conclusion converts to the goal by
unfolding the relation, not the numbers.

The verdict is closed by the interval checker's device
([floating-point-design](floating-point-design.md) §16): the closer takes
`norm_num_true(): norm_num_yes() = True` where its parameter says
`verdict = True`, which converts by evaluating the verdict. `Nat::leb` and
`Nat::same` are folds the kernel runs on numerals of any size
(`crates/kernel/DESIGN.md`, acceleration policy), so a verdict costs the
arithmetic of the two sides and one comparison, linear in their bits, and the
relation itself is only unfolded, never compared numeral by numeral.

Nothing is read off the sides at these carriers: any closed expression that
computes is evaluated whole. `+ - * ⁻¹ ^`, `npow`, `recip`, `inv_succ`,
`abs`, `Int::min`, a decimal literal, a constant defined by a function call:
whatever the kernel reduces. The `Rat` inverse `x⁻¹` carries an apartness
proof, and the value never reads it.

**`CReal`: the embedding's laws over an evaluated rational.** A real is a
sequence, and `≈` between reals is a statement about all of it, so nothing
computes a verdict. The tactic reads each side into a `NumReal` tree whose
`real()` spells each node as the operation it was read from (so a tree's
real converts to the side) and whose `rat()` is the exact value with `Rat`'s
operations. `NumReal::sound(t, w): t.real() ≈ CReal::ofRat(t.rat())` is
proved once, by the laws `ofRat_add`, `ofRat_sub`, `ofRat_neg`,
`ofRat_mul`, `ofRat_npow`, `ofRat_abs`, `ofRat_inv` and the operations'
`respects`. The goal's fact is then the rational one, decided by the `Rat`
verdicts above and carried across the embedding: `ofRat_respects` for `≈`,
`ofRat_lt`/`ofRat_le` with `lt_respects`/`le_respects` for the orders, and
`ofRat_inj`, `lt_of_ofRat_lt`, `le_of_ofRat_le` for the negations.

## 3. Reading `CReal` sides

The nodes are `+`, binary and unary `-`, `*`, `npow`, `^` at an integer
exponent, `⁻¹` and `abs`. Any other real is a leaf when it is
`CReal::ofRat(q)` up to unfolding (a numeral, `third()` defined as
`CReal::ofRat(Rat(1, 3))`): the leaf is `NumQ(norm_num_term(x))`, the
embedding of `x`'s first term, which converts back to `x` exactly when `x`
unfolds to an embedding. The tactic asks that conversion first, so a real
that is not one (a variable, `exp_rat(1)`) fails with "a side is not a
closed real expression" at that real. Unifying `x` with `CReal::ofRat(?q)`
would be the direct reading, but the elaborator does not solve a hole
across the δ-step `third()` needs; the first term needs no hole.

An inverse and a negative power carry a proof about the real they invert,
and a tree cannot carry a proof about its own value (that would be
induction-recursion). So `NumInv(a, x, h)` holds the real `x` the goal wrote
beside the tree `a` read from it, and `Wf` asks that `a` denote `x`, as
`RealExpr::Wf` does for the interval checker; the tactic's witness is
`CReal::same_refl(x)`, by conversion. `sound` moves `h` to the embedding
(`CReal::apart_respects`) and down to the rational (`lt_of_ofRat_lt`), and
the rational value is the reciprocal, which is what `Rat::inv` computes. The
view of a call lists only the arguments it writes, so the `h := infer` an
inverse or a power usually has is not among them: the tactic makes a hole of
the type the node takes and solves it by comparing `CReal::inv(x, ?h)` with
the term read, which meets at the same head and needs no unfolding.

## 4. Refusals

The verdict is asked of the elaborator before the proof is built, so a
failure has its reason, not a refused proof:

- "the goal is false": every way to prove it (two for `Apart`) has a
  verdict that evaluates to the opposite;
- "the two sides do not evaluate to numbers": a verdict is stuck, at a
  variable or an opaque definition;
- "a side is not a closed real expression", at `CReal`, naming the real;
- "`=` is decided at `Nat` and `Int`; … state `≈`";
- "a goal at `CReal` needs `import norm_num_real;`";
- "the goal is not `=`, `≈`, `<`, `<=` or `Apart` between numbers, or the
  negation of one".

An all-numeral relation written bare elaborates at `Nat`
([[all-numeral-relations-default-to-nat]]), and `norm_num` proves what it
states there, as `omega` did: the probes spell `Rat::Lt(0, 1)`.

## 5. Inside other tactics

`norm_num_at(target: Handle) → Tac<Expr>` is the tactic at a given
statement rather than the goal's, for a numeral side goal `linarith`
([[linarith-ordered-fields]]) or `field_simp` ([[field-simp]]) produces;
`attempt(norm_num_at(t))` tries it without failing the caller. Reading is
by global identity (`Lookup`), each carrier's relations looked up only
when the earlier ones did not match, so a client that never imports
`creal` or `dyadic` never resolves their names.

## 6. Costs

Shapes. At the computing carriers, a goal costs evaluating its two sides,
the cross products at `Rat` (two products of a numerator by a denominator),
and one accelerated comparison, linear in their bits; the evaluation runs
three times (the tactic's question, the elaborator's check of the proof,
the kernel's). At `CReal` reading is linear in the sides' size, and the
proof's check is the rational evaluation plus one `respects` step per node.
`Nat::pow(2, 64) * Nat::pow(2, 64) = Nat::pow(2, 128)` and
`(1 + 1/100)^100 < 3` (two-hundred-digit cross products) are probes.

## 7. Not done

- Subterm normalisation inside an open goal (`x + 2 * 3 ≈ x + 6`): that is
  `ring`'s, at `Rat` and `CReal` modulo `≈`
  ([ring-normalization-design](ring-normalization-design.md) §8).
- `min`/`max` are not nodes at `CReal`, which has neither; at `Nat` and
  `Int` they compute.
- `Float(F)` values, which the float literals denote, have only structural
  `=` and the named IEEE comparisons; the tactic reads `Finite(F)`'s
  relations. Deciding `Float(F)` is [[norm-num-float-values]].
