---
title: "Decide: the class of P ∨ ¬P, derived where the relation is recursive"
status: closed
labels: [design,traits,frontend,stdlib]
created: 2026-08-16
updated: 2026-08-20
---

## Final state (updated 2026-08-20; everything below the divider is the filing text)

**The class is complete over the connectives, relations, and equations.**
`docs/language/classes/decide-class-design.md` is the reasoning for the original class round.

Landed in `lib/std/core/logic.hthr`: `class Decide<P> { dec: Or<P, Not(P)> }`, the
constant instances at `True` and `False`, the composition instances at `∧`, `∨`
and `¬`, and the consumers `decide`, `decide_pick`, `decide_pick_yes`. In
`lib/std/num/nat.hthr`: `pred`, `succ_inj`, `IsSucc`, `succ_ne_zero`,
`zero_ne_succ`, `eq_dec` and `le_of_not_le`. The acceptance restatement landed
in full — `lib/lang/list_algos.hthr`'s insertion sort has no `Bool` and no `= True`,
and the before/after is `docs/language/classes/decide-class-design.md` §4.

**A language change was needed and was not the one anticipated.** An instance
may now be keyed at a **type former** (`Not::Decide`), because `¬P` is a `fn`
into `Type` by deliberate choice and the registry keyed only on declared types.
Two design decisions had quietly collided. Details in §2 of the design doc;
the guards were `head_name` and `names_a_type`, and Paterson's decrease
condition had to learn the new carrier syntax with them.

The two gaps found by that round subsequently landed:
[[value-generic-instances]] made `Decide<Le(n, m)>` available at open values,
and [[decidable-equation-carrier]] made `Decide<n = m>` coexist at Nat and
Bool. `lib/lang/list_algos.hthr` consumes the relation instance through `decide`,
and composed propositions containing equations resolve and compute. The
acceptance below is therefore paid in full.

One thing this round *created* rather than found: `Decide` is now the widest
class in the registry at six instances, and selection tries every candidate of
a class. Not measured, not this round's business, and parked on
[[resolution-candidate-fan-out]].

---

A function that branches on a proposition needs a term that produces the
branch. `insert(x, Cons(h, t))` must pick a side on `x <= h` for **arbitrary**
`x` and `h`, so it needs

```heather
class Decide<P> { dec: P ∨ ¬P }
```

and an instance found by resolution. This issue owns that class, its
derivation, and the boundary between it and [[compile-typeclass-design]].

## Why the object must exist, whatever it is called

Three things get confused here, and separating them is most of the design:

1. **Elaboration-time proof search** answers "is `Le(3, 5)` inhabited?" for
   *closed* arguments. It works today and is the `h := infer` case of
   [[guarded-to-option-adapter]]. It cannot serve `insert`, whose body is one
   closed term quantified over all `x` and `h`.
2. **A decider** is that same answer made *uniform*: a term
   `(n, m: Nat) -> n <= m ∨ ¬(n <= m)`. Some such term must exist for
   `insert` to be definable at all; the only alternative is pushing the
   obligation onto every caller. `Decide` is therefore not machinery layered
   on top of the definition — it is the name of a thing the definition
   already requires.
3. **Classical LEM would typecheck and be useless.** An axiom
   `lem : (P: Type) -> P ∨ ¬P` makes `insert` check, and then
   `insert(3, [1,2])` never reduces, because `lem(…)` is a neutral constant
   with no reduction rule. The content of `Decide` versus classical
   disjunction is exactly *"this disjunction reduces"*.

## Why it is not `Bool`, and why there is no sort boundary

`Decide<P>` already **is** the Bool, with the evidence attached; `decide` is
the projection that throws the proofs away. In Lean the two are separate
public objects for two reasons, neither of which applies here:

- **Erasure.** Lean's `Prop` is irrelevant and erased, so a decision cannot be
  eliminated out of it into `Type` — that would observe which proof you were
  handed. Hence `Decidable p : Type` indexed by a `Prop`, a genuine two-object
  split. **Heather keeps proof relevance** (the standing position, restated
  2026-08-16), so `P ∨ ¬P` is an ordinary type and `insert` eliminates it
  directly. No sort boundary, no split.
- **Proof size.** `ble(n, m) = True` is a small proof where a derivation is
  large. Under [[nat-order-kit]]'s recursive `Le` the proposition itself
  reduces to `True` at closed arguments, so reflection is already free and
  this reason evaporates too.

The consequence for the library: **no `Bool` in any spec API and no `= True`
anywhere.** `Bool` stays a data type for when Booleans are the subject
(Boolean algebra, circuits) and inside generated code.

## Derivation, not duplication

The pain to avoid is Lean's: write `Nat.decLe` by hand, prove it correct, and
maintain it beside the relation. A decider for a structurally recursive
proposition is **mechanically derivable from the recursion** — which is the
generator story this project is already built on. Under `nat-order-kit`'s
definition (a), `le_dec` is a five-line structural recursion whose correctness
is definitional; deriving it is the natural next step, not a stretch.

Composition instances are what earn the class rather than a naming
convention: `Decide<P> -> Decide<Q> -> Decide<P ∧ Q>`, the `∨` and `¬` cases,
and the bounded-quantifier cases. Resolution assembles those; a convention
cannot.

**User note (2026-08-16):** `Decide` may later warrant *special* treatment —
a custom elaborator pass automating parts of it beyond what ordinary instance
resolution is smart enough to do — on the grounds that it is core enough to
earn the exception. Recorded as a direction, not scheduled; the ordinary class
comes first and is what would measure whether the exception is needed.

## Decide is not Compile

Recorded as **decided**, answering sub-question 1 of
[[class-ops-prop-vs-bool]]: they stay distinct.

- `Decide<P>` says a case-analysis term exists and reduces. Kerneltime.
- A `Compile` instance says the resulting machine code is sane, with cost and
  representation evidence.

Decidable-but-insane is easy to exhibit (a bounded search over 2^64 cases
decides; nobody should run it), so `Compile` strictly refines `Decide` in
demand, and neither carries the other's content. Three consumers, three
demands: elaboration-time search (closed arguments, needs neither), `Decide`
(uniform kerneltime branching), `Compile` (executable, with cost evidence).

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `Or`/`Not` and the `∨`/`¬` spellings. Assumed here: only that they
  exist.
- **[[class-ops-prop-vs-bool]]** owns the kerneltime/runtime split. Assumed
  here: only its 2026-08-16 log, which this issue's "not Compile" section
  answers rather than restates.
- **[[compile-typeclass-design]]** owns `Compile`. Assumed here: only that it
  demands executable code plus a correctness theorem, which is strictly more
  than a reducing case analysis.
- **[[instance-shorthand-syntax]]** owns one-field instance ergonomics.
  Assumed here: nothing; `Decide` is simply a good customer for it.
- **[[decided-case-convoy]]** owns the elaboration of a case split on a
  decided predicate. Assumed here: only that branching on `dec` is the same
  shape its convoy already handles.

## Acceptance

`le_dec` and `eq_dec` at `Nat`; `insert`/`isort` in `lib/lang/list_algos.hthr`
restated with no `Bool` and no `= True`; the composition instances for `∧`,
`∨`, `¬`; and the restatement's before/after recorded as the measurement of
what the class has to provide (the method [[list-algorithms-exercise]]
established).

## Log

- 2026-08-16: Filed out of the std-API design discussion. The turn that
  produced it: the two-object Prop/Bool split looked foundational until proof
  relevance was reaffirmed, at which point the elimination restriction that
  forces it in Lean simply does not apply — `Decide` drops from a blocking
  design question to a one-field class plus a derivation.
- 2026-08-16: 2026-08-16: The decision procedure this class will be filled with at Nat is WRITTEN, ahead of the class: lib/std/num/nat.hthr's le_dec(n)(m) : Or<Le(n,m), ¬Le(n,m)>, plus le_bool_dec at Bool, and Cmp carries a le_dec field until Decide exists to be a superclass constraint instead ([[nat-order-kit]], docs/library/nat-order-design.md §2). Three findings this class inherits. (1) A decider must be a fn, not a theorem: a theorem is opaque, so it never unfolds in conversion and max_of(2,5)=5 stops being refl. The kernel found this, not reasoning. (2) Deciders reduce at closed arguments, so decider-driven branching is refl-provable today with no Decide class and no reflection — the derived-where-structurally-recursive claim is cheap at Nat (le_dec is nine lines and mirrors Le exactly). (3) The consumption shape is logic::or_pick_dec: a dependent match whose motive reaches its own scrutinee, refuting arm closed by the caller's proof, no equation and no transport. That is what an if-on-a-proposition desugars to, and it is simpler than the Bool version it replaced.
- 2026-08-17: Landed, complete over the connectives (True/False/And/Or/Not) and absent at the relations. Three findings the filing did not predict. (1) The head-key restriction that refused Not/Le/= is NOT layer 2's deferred (class, carrier-syntax) key: resolution filters on the class key alone and tries every candidate by convertibility, so the head is a declaration-time naming device only. The fix was widening head_name to applied type formers plus an owner rule admitting type formers — about thirty lines, not a layer. (2) Paterson's decrease condition measured OfExpr carriers as size 1 / zero occurrences, so every instance at an applied former would have refused whatever it required; ty_size and ty_var_count now walk the application spine. (3) The motivating example is still unreachable, for a different reason than the one scoped: an instance cannot bind an ordinary value parameter, so instance Decide<Le(n, m)> has no spelling ([[value-generic-instances]]). Decide<Le(2, 5)> registers and is useless. docs/language/classes/decide-class-design.md is the record; the list_algos restatement traded thirteen declarations for two and lost every j, trans and congruence.
- 2026-08-17: The blocker this issue's §'What is left' named is gone: [[value-generic-instances]] landed 2026-08-17, and Decide is now complete over the relations as well as the connectives. std/nat declares `instance(n, m: Nat) Decide<Le(n, m)>` and list_algos's three call sites read `decide<Le(x, h)>()`, so no declaration there names a decision procedure any more. The restatement's measurement (§4 of the design doc) was taken before this and is unchanged by it — the proofs did not move, because Le::Decide.dec unfolds to le_dec(n)(m) and conversion never saw a difference. Equations are still out, on the key ([[decidable-equation-carrier]]), which is the boundary §3.1 drew and it held.
- 2026-08-20: Closed after auditing the final boundary against
  [[decidable-equation-carrier]]: Nat and Bool equality instances coexist,
  open relation instances resolve, and proposition-directed branching plus
  connective composition compute through both. No `Decide` scope remains.
