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

## 4. The refusal: a binder must occur in the head

```
the type parameter `A` does not occur in the head `Dec<Bot>`, so resolution has
no way to determine it …
```

There is one route by which a binder is determined — unification of the head
against the goal — so a binder the head does not mention is a metavariable
**nothing can ever solve**. Left unchecked such an instance still declares, and
it costs twice: a rejection at every use site instead of one at the declaration,
and a registry entry no goal can use that **every goal must still try**, since
selection walks every candidate of a class in sorted order
(`issues/resolution-candidate-fan-out.md`). The second is the one a reader never
sees.

The message routes the three wishes a head-absent binder usually expresses, two
of which have a spelling that works:

- *"a family of instances selected by a value"* — that is a class **index**
  (`class C<A>(op)`), which joins the registry key, so `Monoid<Bool>(and)` and
  `Monoid<Bool>(or)` coexist as equals. A head-absent binder expresses the same
  wish and fails at it: both instances would be one entry at one key.
- *"a value I will fill by hand"* — a `fn`. It is the same value without a
  registry entry, and `@`-applying a named instance is strictly worse: it pays
  the fan-out cost for a candidate that cannot succeed.
- *"resolution should pick one"* — unavailable, deliberately. The resolver
  selects among candidates and never guesses an argument, so
  `instance<A> Serialize<Nat> requires enc: Encoder<A>` is exactly the request
  the language declines, and declining it at the declaration says so once.

### 4.1 The rule is not uniform, and that is the finding

Stated for value binders when this round landed and **extended to type
parameters on 2026-08-17** (`issues/instance-binder-occurrence.md`). The
asymmetry that existed in between was unexamined rather than decided, and this
section previously claimed otherwise; what the examination found is that the
rule *is* asymmetric, just not where it had been drawn:

| binder | counts |
|---|---|
| type parameter | class arguments **and** index |
| value binder | class arguments **and** index |

A **type parameter may occur in an index**, and usefully — an index argument may
be a global reference at this instance's own type parameters, and the index is
part of the class type, so a goal determines it there.
`instance<A> Mag<Bool2>(pick<A>)` both declares and resolves, and a rule
counting class arguments only would refuse it. Since 2026-08-31 a **value
binder may occur in an index too**: candidate-head unification recovers it from
the goal, while `index_spelling` uses its binder position to mint an
alpha-stable, unwritable registry component. Thus `instance<A>(n: Nat)
CollectionLiteral<List<A>>(n)` represents one generic instance, not a slot
whose identity depends on whether its writer called the binder `n` or `k`.

So the two kinds differ in *where a goal can determine them from*, and the check
follows that rather than being tidy. `head_var_count` and `index_var_count`
are the two halves.

### 4.2 What the extension cost

The original type-parameter extension changed nothing in the repository: no
declaration in `lib/` and no test in the suite used the loophole, measured by
turning the check on and running the full suite (1762 passed, 0 failed). Nor was
the old behaviour *broken* — `instance<A>
Dec<Bot>` declared, refused to resolve with a diagnostic that named the
candidate, the reason and the escape, and `Bot::Dec<Nat>.d` worked by hand. The
extension buys earliness, one rule instead of two, and the fan-out entry; it is
not a rescue, and saying so is the honest size of it.

Two ordinary hygiene refusals come with the value list: a value binder may not
repeat a name, and may not shadow one of the instance's own type parameters.

### 4.3 Value-indexed classes do not mint derived specializations

The canonical derived-instance table deliberately skips classes with value
parameters. An open index cannot become an empty-context global; a closed one
can, but each distinct value would mint a synonymous specialization of the
same declared parameterized instance. Resolution keeps that application
directly instead. This gives collection-literal lengths and operation indices
one uniform policy and avoids unbounded global growth at the cost of optional
sharing only.

### 4.4 Amendment (2026-09-24): occurrence in the *elaborated* head

§4's rule counted a binder's name in the **written** class arguments. What
candidate unification actually matches against a goal is the **elaborated**
head, and elaboration writes binders the source does not name:

- an equation's endpoint type: `Decide<xs = ys>` at `xs, ys: List<A>` is
  `Id(List<A>, xs, ys)`, so `A` is recovered with `xs` and `ys`;
- a call's inserted implicits: `Decide<BitVec::unsigned_lt(a, b)>` at
  `a, b: BitVec(n)` is `unsigned_lt(n, a, b)`.

The rule now accepts a binder that is absent from the written head but
present in the elaborated class arguments (`binder_in_elaborated_head` in
`crates/elab/src/traits.rs`). It runs only when the written count is zero,
so a head that names its binders is never elaborated by the check. The index
is still not consulted, because it joins the key as a spelling.
`instance<Q> Dec<Top>` and `instance(k: Nat) Dec<Top>` are still refused,
since nothing determines `Q` or `k` in either head.

§5's variable condition had the same blind spot: `requires DecEq<A>` against
a head that names `A` only through elaboration read as "mentions `A` more
often than the head does". A binder the check finds only in the elaborated
head now counts once there. That is a lower bound on its true occurrences,
so the condition can only refuse more than an exact count would, never
accept more.

This made two library rows expressible. `lib/std/list.hthr` now has
`instance<A: DecEq>(xs, ys: List<A>) Decide<xs = ys>` in place of the
`List<Nat>`-only instance, and `lib/std/bitvec.hthr`'s four order instances
drop their `@`. The list instance also needed a unifier change: the goal's
endpoint type, inferred from constructor values, is the *inline* lowering,
while the instance's `List<A>` is the declaration's reference.
`docs/unifier-completeness-design.md` §10.2 is that change.
(`issues/instance-binder-occurrence-through-binder-types.md`.)

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

Both halves measure the class arguments only. For a value binder that is §4's
measure exactly, and for the same reason — one that reaches only the index is
refused outright. For a *type* parameter it is deliberately narrower than §4.1's
recovery rule: a subgoal mentioning a type parameter that lives only in the
index admits no decrease, which refuses programs rather than admitting bad ones.
Loosening a termination check to match a recovery check is not a step to take
without a customer, and the library has none — every instance of an indexed
class in `lib/` (`Monoid<List<A>>(append)` and its neighbours) writes its type
parameter in the class arguments, where both measures already see it.

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
- ~~**The occurrence rule at type parameters**~~ — extended 2026-08-17, §4.1
  (`issues/instance-binder-occurrence.md`). What looked like a consistency fix
  turned out to have content: the rule is genuinely asymmetric, because a type
  parameter can be determined from an index and a value binder cannot.
- **An instance generic in its *index*** (§4.1) is a coherent feature this one
  does not provide, and the refusal names it as such. It wants the index to stop
  being a spelling in the registry key, which is a bigger question than a binder
  list — and nothing asks for it yet.
