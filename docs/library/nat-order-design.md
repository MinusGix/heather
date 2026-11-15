# Nat's order, stated in Prop

Design doc for `issues/nat-order-kit.md` (wave 1 of `issues/std-api-waves.md`),
landed 2026-08-16. The claim being designed: `Nat`'s order is a *proposition*,
stated once, with no `Bool` and no `= True` in its specification — and nothing
is lost in the move, because the proposition computes.

This is the first library file written under `issues/class-ops-prop-vs-bool.md`'s
2026-08-16 direction (privilege Prop, keep proof relevance, let the compiler do
erasure). It is therefore also the measurement of what that direction costs,
and §5 is the answer.

## 1. The definition

```heather
fn Le(n: Nat) -> Nat -> Type {
    match n {
        Zero => λ (m: Nat) => True,
        Succ(k) => λ (m: Nat) => match m { Zero => False, Succ(l) => Le(k)(l) },
    }
}

fn Lt(n, m: Nat) -> Type { Le(Succ(n), m) }
```

Route (a) of the issue's three, and the three properties that chose it are all
visible in `lib/std/num/nat.hthr`'s bodies rather than argued for:

- **It reduces.** `Le(3, 10)` normalises to `True`, so `zero_le` is `trivial`
  and a closed comparison is proved by the kernel computing rather than by
  anyone traversing a derivation. This is proof-by-reflection with no `Bool`,
  no `decide` and no bridge lemma — the reason the `= True` idiom existed, had
  outright.
- **Inversion is definitional.** `Le(Succ n, Succ m)` and `Le(n, m)` are the
  same type, so `le_succ_succ` and `le_of_succ_succ` are both the identity
  function, and `le_total`'s successor step is `ih(m2)` with no repackaging.
- **Absurd cases are already `False`.** `not_succ_le_zero(n, h)` returns `h`.

**Curried, and not by preference.** The uncurried spelling is refused — the
inner `match` makes the recursive call vary both arguments, and the guard
requires the descending one to pass unchanged (`issues/ih-generalization.md`).
`leb` and `sub` were already curried for this reason, so the shape is the
file's idiom rather than a new tax, and over-application means `Le(n, m)`
writes everywhere anyway.

**`Lt` is a definition, not a second recursion.** Everything `Le` computes,
`Lt` computes, and the two facts a reader wants most are definitional:
`lt_succ_self` is `le_refl(n)`, and `lt_succ_iff_le` is a pair of identity
functions.

**Route (c) is proved, not chosen.** `le_iff_exists_add` gives
`n <= m ↔ ∃ k, n + k = m` as a *view*, so a proof that is shorter in the
additive presentation can be written there. That is what makes the definition
swappable: the discipline is that **downstream never unfolds `Le`**, and
`lib/certgen/ir_v1.hthr` — the largest consumer, with eight uses — went through this
round **unmodified**, which is the evidence the discipline was already held.
Route (b), the indexed family, is still the right technique for relations `Le`
cannot express and is unaffected by any of this.

## 2. Deciding, without a `Decide` class

A propositional order still has to pick values, and the decider is the whole
of what replaces the `Bool`:

```heather
theorem le_dec(n: Nat): (m: Nat) -> Or<Le(n, m), ¬ Le(n, m)> { … }
```

`Or` and `Not` are `std/logic`'s (wave 0). Two things about this are worth
recording because both were checked rather than assumed:

1. **It reduces at closed arguments**, so a decider-driven branch is still
   `refl`-provable — `max_of(2, 5) = 5 { refl }` survives the conversion. This
   was the round's first probe and it is the fact the whole design rests on.
2. **The decider and its branch must both be `fn`s.** A `theorem` is opaque,
   so it never unfolds in conversion. `logic::or_elim` computes exactly what
   `or_pick` does but is a `theorem`, so `or_pick` is a `fn`; and `le_dec`
   itself was written as a `theorem` first and the kernel rejected
   `max_of(2, 5) = 5` with `NotConvertible` until it became a `fn`. *Deciding
   is computation*, and the rule is not about the return type — a `fn`
   returning a proposition is still a definition, which is what a decision
   procedure has to be. Both notes are carried in the source where the two
   declarations are.

`issues/decide-class.md` owns the general `Decide` class. Nothing here waits
for it: a `le_dec` field is a local decision about one class, and when `Decide`
lands the field becomes a superclass constraint with no consumer moving.

## 3. `Cmp` goes propositional

```heather
class Cmp<A> {
    le: A -> A -> Type,
    le_refl: (x: A) -> le(x, x),
    le_dec: (x, y: A) -> Or<le(x, y), Not(le(x, y))>,
}
```

Replacing `le: A -> A -> Bool` with `le_refl: (x: A) -> le(x, x) = True`.

**The proof side got simpler, which was not predicted.** The old
`max_of_true` had to `j`-rewrite a stuck `Bool` to `True` before `cmp_pick`
would reduce. Its successor `max_of_le` calls `or_pick_dec`, whose proof is a
dependent `match` on the decider whose motive reaches its own scrutinee:

```heather
theorem or_pick_dec<P, A>(d: Or<P, Not(P)>, x, y: A, p: P): or_pick(d, x, y) = y {
    match d as λ z => or_pick(z, x, y) = y {
        Inl(good) => refl,
        Inr(bad) => false_elim(bad(p)),
    }
}
```

No equation and no transport. The refuting arm is closed by the proof the
caller already holds — which is available *because* propositions are relevant,
and is the concrete thing `issues/class-ops-prop-vs-bool.md`'s decision (4)
buys at a use site.

**The rename is the content.** `max_of_true(x, y, p: x.le(y) = True)` became
`max_of_le(x, y, p: A.le(x, y))`: the hypothesis is the relation itself rather
than a fact about having run a decision procedure.

`leb` and `bool`'s Boolean decision **stay**, as decision procedures. (The
latter was `leb_bool` until 2026-08-17 and is `bool::leb` now: the module is
the namespace, and the suffix existed only because the instance registry keyed
on written names — `docs/elaborator/instance-resolved-key-design.md` §6.) `lib/lang/list_algos.hthr`'s
`sortedb`/`insert` kit and `lib/certgen/certgen_code.hthr` are written against them and
are not this round's to restate (`issues/std-api-waves.md` L3 owns that, behind
`Decide`). What changed is their standing: nothing in a *specification* names
them, and `Cmp` no longer does.

> **Superseded in part, 2026-08-17.** `list_algos`'s insertion sort *was*
> restated — `Sorted` is a recursion into `Type` and `insert` decides with
> `le_dec` — so `leb`'s last specification customer is gone and only
> `certgen_code` still reads it, where a Boolean is the subject rather than the
> statement. See `docs/language/classes/decide-class-design.md` §4 for the before/after. The
> sentence above is kept because it records what the order round chose to defer
> and why, which is still the reason the restatement was a separate round.

## 4. Two grammar findings, both from writing the file

**`<` was unusable in a type position, and the issue said it wasn't.**
`issues/nat-order-kit.md` recorded that `<` already lexes at the comparison
rung, so `Lt` would be "a library declaration plus a designation row, not a
grammar change". That is refuted: `h: i < len(xs)` failed to parse, because
`Parser::ty` read every `ident <` as the start of type arguments. The comment
justifying that said "`<` is the `lt` operator only in *expression* position,
and no expression is a type" — **a premise that dies exactly when the order
becomes propositional**, since `n < m` is then a type, written precisely where
a hypothesis is. Since `Lt`'s four listed uses (termination measures, `Fin`
and bounds, trichotomy, strict monotonicity) are all `<` in a hypothesis
position, shipping `Lt` without this would have shipped half of it.

The fix is **speculative parsing**, not lookahead, because no bounded lookahead
decides it: `D<A, B>` and `a < b` agree for arbitrarily many tokens (compare
`f(x) < g(y)` with `Vec<Pair<A, B>>`). `Parser::ty` already rewound to a saved
position for two narrower discriminators — a following `(`, and a following
connective — so this is the same `save` covering the largest case: try the type
arguments, and if that parse does not *complete*, it was the operator.

**The residue this round left has since been fixed** — see
`docs/language/type-argument-disambiguation.md`, which owns the rule now. As landed
here, a `<` nested directly inside type arguments needed parentheses
(`Or<(n < m), (m <= n)>`), and the diagnosis in this paragraph was wrong: the
inner `ty()` does not "stop at the `<`", it *speculates and succeeds*, eating
the outer list's closing `>`. That is why no widening of the argument grammar
could have fixed it, and why the answer turned out to be whitespace — a `<`
with a space before it never opens a list, so the inner one cannot take the
outer's bracket. Parentheses still work; they are no longer required.

**`∃` does not reach a type-argument slot.** `Iff<Le(n, m), ∃ (k: Nat), …>`
cannot parse (the binder's `,` is the type-argument separator) and
parenthesising does not rescue it, since a parenthesised quantifier is not a
type either. `le_iff_exists_add` is written with the call spelling,
`Exists(λ (k: Nat) => add(n, k) = m)`, which is what wave 0 shipped and is
fine; the notation gap is filed.

## 5. What the Prop-first direction cost, measured

The round is the first evidence for `issues/class-ops-prop-vs-bool.md`'s
direction, so the bill is worth stating plainly.

- **Downstream migration: zero.** `lib/certgen/ir_v1.hthr` and `lib/lang/list_algos.hthr`
  both check unmodified. The definition of `Le` changed underneath eight uses
  and none of them noticed, because all eight go through the lemma kit.
- **The `Cmp` conversion: three field spellings and two instances**, plus one
  proof that got shorter (§3).
- **`false_elim` had to change shape**, and this is the one place the library
  itself was wrong. `false_elim(P: Type, h: False)` takes its goal as a *value*
  parameter, which forces an absurd arm to spell its own goal — long, and
  where the spelling needs a type argument nothing determines, impossible
  (`or_pick(Inr(bad), x, y) = y` cannot infer `Inr`'s left type argument). As
  a **type** parameter, `false_elim<P>(h: False): P`, it is filled from the
  checking position the arm is already in and `false_elim(bad(p))` writes.
  `absurd_of` took the same treatment. Wave 0 shipped both spellings one day
  earlier; nothing had used them in an absurd arm yet, which is precisely the
  position they exist for.
- **The one real cost is the one the issue predicted:** `Le` is a definition
  that unfolds, so a goal can display as `True` rather than `n <= m`, and
  conversion may unfold it where a reader would rather it did not. No
  irreducibility control exists yet. Nothing in this round was blocked by it.

## 6. What is not here

`min`/`max` at `Nat`, the `sub` kit beyond `sub_zero`, and the arithmetic
interaction lemmas (`add_le_mono`, `mul_le_mono`, cancellation) are wave 1 and
wave 3 content deferred by the round's charter to keep one reviewable diff;
`issues/nat-order-kit.md` carries them. `min`/`max` at `Nat` in particular need
no decision at all — they are plain structural recursions — which remains the
standing correction to the assumption that a "decided" function needs a
decider.

**Landed 2026-08-17** under `issues/nat-arithmetic-kit.md`, which took
ownership of the list above when the order issue closed. The prediction held
exactly: `min`/`max` mention no decider, and every monotonicity and
cancellation lemma is an induction on the operand being added on, where a step
of the induction is a step of `add` and a step of `Le` cancelling — so the arm
is the IH applied unchanged. The one shape the section pays for is the `_l`
half of each pair, which is the `_r` half transported through commutativity
with `j`, because `add` descends on its second argument. Nothing in that round
was blocked by the irreducibility gap named above either, but it is now the
most likely place to *see* it: a goal about `Le` at open arguments is an
`El(code)` that never reaches a non-`El` head, so the display reader falls back
to the raw form (`issues/le-diagnostics-print-raw-el.md`).
