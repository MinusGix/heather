# An instance generic over a **value**: `instance(n, m: Nat) Decide<Le(n, m)>`

Specification slice for `issues/value-generic-instances.md`, landed 2026-08-17.

Before this, an instance could be generic over **types**
(`instance<A> Monoid<List<A>>`) or fixed at a value **index**
(`instance CommMonoid<Nat>(add)`), and nothing bound an ordinary value
parameter. The gap was not academic: `docs/decide-class-design.md` §3.2 records
that it was the single thing standing between `Decide` and the example the
class was filed for, and that the only registrable spelling —
`instance Decide<Le(2, 5)>`, at fixed numerals — was exactly the case
elaboration-time computation already answered. The reachable case was the
worthless one.

Companion records: `docs/traits-layer1-design.md` (the canonical name and the
instance assembler), `docs/traits-layer2-design.md` (resolution, §6's decrease
discipline), `docs/decide-class-design.md` (the class this unblocks),
`docs/surface-value-parameters.md` (the `record` head this borrows its
production from).

## 1. The finding: the machinery was already there

The round was small, and the reason is worth stating before the design.
Resolution builds a candidate by elaborating the instance's global **in
checking position against the goal** (`resolve.rs::build_candidate`, layer 2
§3.2), which is what supplies `instance<A> Monoid<List<A>>` with its `A`. A
metavariable inserted for an *implicit value* parameter is solved by that same
unification, and the unifier already decomposes an application spine headed by
a `fn` — `Le(?n, ?m)` against `Le(x, h)` at open `x` and `h` — because `Le` is
defined by recursion on its first argument, so both sides are stuck at the same
global and neither side reduces.

That was measured before anything was written, with a hand-rolled global:

```heather
fn ld({n: Nat}, {m: Nat}) -> Decide<Le(n, m)> { Decide(le_dec(n)(m)) }
fn probe(x: Nat, h: Nat) -> Decide<Le(x, h)> { ld }   // ok
```

A bare `ld` in checking position is precisely what `build_candidate` writes. So
what was missing was **a binder list and nothing else**: no unifier work, no
resolver work, no change to the registry key. The issue guessed this ("the same
machinery `instance<A> Monoid<List<A>>` already needs") and the guess held.

## 2. The spelling: a parameter list at `instance`

```heather
instance(n, m: Nat) Decide<Le(n, m)> { dec := le_dec(n)(m) }
```

The two candidates were a parameter list and a trailing `forall`. The parameter
list wins on the parse constraint that killed the obvious route elsewhere:
`requires n: Nat` is ambiguous because `requires` already takes a list of class
references, but `(` immediately after `instance` begins **nothing else** — the
head is a class reference and a class reference starts with an identifier. So
the grammar addition is a single optional list at a position that was a parse
error, and `docs/surface-value-parameters.md` §1's objection does not reach it.

It is the *same production* a `record` or `class` head takes
(`parser.rs::valparam_list`), not a new one. Two consequences:

- A **grouped run** (`(n, m: Nat)`) now parses in all four heads, not only in
  this one. It was a parse error everywhere before, so the change is strictly
  additive, and it is shared rather than special-cased here because a reader who
  has written `fn f(n, m: Nat)` has no way to know the head is a different
  production. Being told `expected ':'` for a spelling the language accepts one
  line up is not a boundary worth defending.
- A value binder therefore cannot carry `as ∙` notation, `self`, `:= infer`, or
  an explicit `{…}` marker — none of them parse in that list, and each is
  already refused with its own message.

## 3. The desugaring: implicit parameters, ahead of the solver parameters

Every value binder is marked `implicit: true` **in the parser**, at the one
place both instance body forms pass through. A use site never writes them:
resolution recovers them by unifying the head against the goal, exactly as it
recovers `instance<A>`'s type parameters, and `@`-marking an instance value by
hand is the escape that already exists for the type case.

The instance's telescope after its type parameters is then

> value binders, then solver parameters (`requires` and the inline `<A: C>`
> constraints)

— `traits.rs::instance_params`, used by both consumers, the synthesized
declarations (the assembled value, the canonical parents, the agreement
certificates) and the block members. Value binders lead because a `requires`
type may mention one (`instance(n: Nat) C<F(n)> requires D<G(n)>`) and the
converse cannot happen: a solver parameter's type is a class type, and no
binder's type is written in terms of a dictionary.

An instance with value binders is `parameterized`, which it has to be: its
value is a function, so it offers neither fill-by-reference nor an agreement
partner to a child instance (layer 1 §8), and that was already the rule for
`instance<A>`.

Nothing about the **registry key** changes. `Le(n, m)` keys at `Le` perfectly
well; the head has never carried the carrier's arguments, and resolution never
consults the head at all (`docs/decide-class-design.md` §2.2). The issue said
this was not the canonical-name problem and it was right.

## 4. The one new refusal: a binder must occur in the head

```
the value binder `k` does not occur in the head `Decide<True>`, so resolution
has no way to determine it …
```

There is exactly one route by which a value binder is determined — unification
of the head against the goal — so a binder the head does not mention is a
metavariable **nothing can ever solve**. Left unchecked, the failure surfaces
far from the declaration, as an uninstantiated implicit at some unrelated use
site. It is checked at the declaration, where the name to blame is in hand.

The occurrence is counted over the **class arguments** only. Occurring in the
*index* does not count, and that is the second refusal rather than an
approximation:

```
the value binder `k` occurs only in this instance's index, which is not a
position a binder can be recovered from …
```

An index argument joins the registry **key** as a *spelling*, computed from the
declaration alone (`docs/operation-indexed-classes-design.md` §3.1), and a local
binder has no spelling: `index_spelling` falls back to the name as written, so
`instance(k: F) Monoid<Nat>(k)` would key under `k`, two instances differing
only in what they called their binder would land at different keys, and two
agreeing on it would collide. It is refused with its own sentence because the
generic complaint — "does not occur in the head" — reads as false to someone
looking at `Monoid<Nat>(k)`.

An instance generic in its *index* is a coherent thing to want and a different
feature from this one; nothing asks for it yet.

This condition is **not** imposed on type parameters, and the asymmetry is
deliberate rather than an oversight: `instance<A> C<Rat>` has been accepted
since layer 1, and tightening it is a separate change with its own blast radius
over the standard library. The rule is stated for the binders this round
introduces, where there is no history to break.

Two ordinary hygiene refusals come with it: a value binder may not repeat a
name, and may not shadow one of the instance's own type parameters.

## 5. Termination: Paterson's condition counts value binders

`check_decrease` (layer 2 §6) enforces that each `requires` subgoal is
structurally smaller than the head, in two parts — a size comparison and a
variable-occurrence comparison. The second now ranges over value binders as
well as type parameters, because a value binder duplicates exactly as a type
parameter does:

```heather
instance(n, m: Nat) Decide<Le(n, Succ(m))> requires h: Decide<Le(n, n)>
//                          refused: mentions `n` more often than the head does
```

The size half needed nothing: `ty_size`/`ty_var_count` learned to walk an
applied type former's spine during the carrier widening
(`docs/decide-class-design.md` §2.3), and a value argument is a node on that
spine like any other.

Both halves measure the class arguments only, which is the same measure §4's
occurrence rule uses and for the same reason: a value binder that reaches only
the index is refused outright.

## 6. What it bought

`std/nat`:

```heather
instance(n, m: Nat) Decide<Le(n, m)> { dec := le_dec(n)(m) }
```

one line, and with it `list_algos`'s `insert` decides **through the class**:

| before | after |
|---|---|
| `or_pick(le_dec(x, h), …)` | `or_pick(decide<Le(x, h)>(), …)` |
| `match le_dec(x, h) as λ d => …` | `match decide<Le(x, h)>() as λ d => …` |

Three call sites, and no declaration in `list_algos` names a decision procedure
any more — the file states the proposition and the class finds the decider, at
an `x` and an `h` that are open. That is the acceptance
`issues/value-generic-instances.md` asked for, and it is a substitution and not
a rewrite: the proofs are unchanged, because `Le::Decide.dec` unfolds to
`le_dec(n)(m)` and conversion never saw a difference.

Backchaining reaches it too, which is the part that is not a rename:
`decide<Not(Le(x, h))>()` and `decide<And<Le(x, h), Le(h, x)>>()` resolve at
open arguments by composing the connective instances of `std/logic` over this
one. Before, every such goal died at the `Le` leaf.

`decide_pick` still **computes** — `pick(2, 5)` is `refl`-provably `2` — which
is the property the "a decider is a `fn`, never a `theorem`" discipline exists
to protect, and the reason the instance is registered at `le_dec` rather than at
a proof of the same disjunction.

## 7. Residue

- **`Decide` at an equation** is still unreachable, and for the unrelated
  reason: `n = m` has no head to key on
  (`issues/decidable-equation-carrier.md`). The two gaps §3 of the `Decide`
  record called independent stayed independent, and closing this one moved that
  one not at all.
- **Candidate fan-out.** `Decide` now has seven instances, and selection tries
  every candidate of a class in sorted order until one checks
  (`issues/resolution-candidate-fan-out.md`). Not measured — per `CLAUDE.md`
  this was not a perf round — but the new instance makes the class the widest in
  the registry by one more.
- **The occurrence rule at type parameters** (§4) is unstated for `instance<A>`
  and would be the natural companion tightening.
- **An instance generic in its *index*** (§4) is a coherent feature this one
  does not provide, and the refusal names it as such. It wants the index to stop
  being a spelling in the registry key, which is a bigger question than a binder
  list — and nothing asks for it yet.
