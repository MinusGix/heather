# `Decide`: the class of `P ∨ ¬P`, and the carrier widening it needed

Specification slice for `issues/decide-class.md`, landed 2026-08-17. What the
issue asked for and what the language turned out to allow differ, in two places
that are worth reading before the class itself — so §2 and §3 come first, and
§1 is short.

Companion records: `docs/traits-layer1-design.md` (the canonical name, §4.1 and
§7.1), `docs/traits-layer2-design.md` (resolution and the decrease discipline),
`docs/nat-order-design.md` (the propositional `Le` this decides).

## 1. The class

```heather
class Decide<P> { dec: Or<P, Not(P)> }
```

One field. `Decide<P>` already *is* the Bool with its evidence attached, and
there is no sort boundary to cross: Heather keeps proof relevance, so a `match`
on `dec` eliminates straight into `Type` and no `Decidable`-indexed-by-`Prop`
split is forced. That is the whole of why this is a one-field class here and a
two-object design in Lean; `issues/decide-class.md` argues it and is not
restated.

The content of the class is **"this disjunction reduces"**. A classical
`lem : (P: Type) -> P ∨ ¬P` makes every consumer typecheck and then compute
nothing, because `lem(…)` is a neutral constant with no reduction rule.

## 2. The carrier widening: an instance may be keyed at a **type former**

This is what the round actually cost, and it was not the thing the issue
expected to pay for.

### 2.1 What refused, and where

An instance's canonical name is `{Head}::{Class}`, where `Head` is the head
name of the carrier (`traits-layer1-design.md` §4.1). Two guards enforced it,
and both refused every proposition that is not a declared type:

- `head_name` (`crates/elab/src/traits.rs`) answered only for `TyKind::Nat` and
  `TyKind::Named`. A proposition stated by recursion into `Type` arrives as
  `TyKind::OfExpr(App{..})` — `Le(n, m)`, `Not(P)` — and fell through to
  `None`.
- `names_a_type` (`crates/elab/src/lib.rs`) required the head to be a declared
  inductive or a kernel type. `Le` and `Not` are `fn`s, so even with a head in
  hand, `Le::Decide` "attached to nothing".

The measured consequence: of the five carriers `issues/decide-class.md`'s
acceptance names, `∧` and `∨` worked already and `¬`, `Le` and `=` all refused,
with one diagnostic between them.

### 2.2 What the guards were actually protecting

**Not resolution.** This is the finding that made the round small. The resolver
(`crates/elab/src/resolve.rs`) selects a candidate by filtering the registry on
the **class key alone** and then elaborating each candidate in checking position
against the goal:

```rust
let mut cands: Vec<(String, bool, String)> = self
    .instances.iter()
    .filter(|((c, _, _), _)| *c == ckey)
```

The carrier head never enters the search. It is a *declaration-time* device: it
mints the canonical name and it detects duplicates. So the (class,
carrier-syntax) key that §7.1 and §8 defer to layer 2 — which is what a reader
of those sections would reach for here — is not what was blocking `Decide`, and
implementing it would have bought nothing this class needed.

§7.1's stated evidence for head-keying is that the name has to be *spellable*
"in a layer without resolution". Layer 2 has a resolver, so that premise has
partly expired; what survives is that the name still has to be an identifier,
which head-keying still delivers.

### 2.3 The widening

`head_name` gains the applied-type-former case, yielding the former's own name.
`names_a_type` gains a companion, `names_a_type_former` — a global whose type,
after every argument is peeled, is a universe — and the two are used through one
predicate, `names_a_carrier`.

**Type formers and not merely any global**, because the name has to keep meaning
what it says: `Le::Decide` reads as "the `Decide` at `Le`", and that is a
sentence only when `Le` is something a proposition can be *of*. A global
returning `Nat` still refuses.

The owner rule is widened at the **member-declaration** check, not only on the
instance path, so that a type former owns a namespace uniformly. An instance's
canonical name has never been a special kind of declaration, and making it one
to avoid touching that check would have been the first time it was.

Two consequences worth stating plainly:

- **Duplicate detection coarsens.** Every `Decide<Le(…)>` collides at key `Le`
  regardless of arguments. That is the same narrowing already accepted for
  `Monoid<Pair<A, B>>` and it is a declaration error naming both, never a
  silent overwrite.
- **Paterson's condition had to learn the new syntax.** `ty_size` and
  `ty_var_count` fell through to `1`/`0` for `TyKind::OfExpr`, which was
  harmless only while such a carrier could not be declared — a head of size 1
  admits no strictly smaller subgoal, so *every* instance at one would have
  refused whatever it required. Both now walk the application spine, and
  `instance<P: Decide> Decide<Not(P)>` is admitted because `P` is strictly
  smaller than `Not(P)`.

`True` was also missing from `names_a_type` — a kernel type claimed as a surface
name with no declaration behind it, exactly like `Nat`, and simply not listed.

## 3. What `Decide` still cannot reach

Two boundaries, and they are different from each other. Neither is a defect in
the class.

### 3.1 An equation has no head — the genuine layer-2 case

`Decide<n = m>` refuses, and `head_name` **deliberately** does not answer for
`TyKind::Eq`. One reserved key would collide `n = m` at `Nat` with equality at
every other type, so keying it needs the endpoints' type in the key — which is
the (class, carrier-syntax) key of §7.1, wanted here for real.

`std/nat`'s `eq_dec` is therefore an ordinary `fn`, called by name.
`issues/decidable-equation-carrier.md` owns the key.

### 3.2 An instance cannot be generic over a **value**

This is the sharper one, and it is what stands between `Decide` and the example
the issue was filed for. `insert(x, Cons(h, t))` needs to decide `Le(x, h)` at
**open** `x` and `h`, so it needs

```heather
instance Decide<Le(n, m)>          // generic in n, m : Nat
```

and there is no spelling for it. An instance may be generic over *types*
(`instance<A> Monoid<List<A>>`) or carry fixed value *indices*
(`CommMonoid<Nat>(add)`), but nothing binds an ordinary value parameter:
`requires` accepts only class references, and `docs/surface-value-parameters.md`
§1 records why a value list there would be ambiguous.

So `Decide<Le(2, 5)>` — closed — registers fine and is useless, because
elaboration-time search already answered that case. The open case, which is the
only one `insert` has, is unreachable. `issues/value-generic-instances.md` owns
it.

**The class is therefore complete over the connectives and absent at the
relations**, and the relations keep deciding the way they already did: by
calling `le_dec`, or through `Cmp`'s `le_dec` field.

## 4. The measurement: `list_algos` restated

`issues/decide-class.md`'s acceptance asks for `insert`/`isort` with no `Bool`
and no `= True`, and for the before/after to be recorded as what the round
bought. It is one-sided.

**Gone — thirteen declarations.** `andb`, `le_head`, `sortedb`, `ins_pick`; the
four congruences `cong_sortedb`, `cong_le_head`, `cong_andb_l`,
`cong_ins_pick`; the three `andb_true`/`andb_true_l`/`andb_true_r`; and
`leb_false_flip`.

**Arrived — two, plus one line elsewhere.** `LeHead` and `Sorted`, both
recursions into `Type`, and `le_of_not_le` in `std/nat`.

Three substitutions carry the whole difference:

| before | after |
|---|---|
| `andb_true_l` / `andb_true_r` | `hs.left` / `hs.right` — `And` is a record, so elimination is field access |
| `leb_false_flip`, an induction on `x` with `y` generalized | `le_of_not_le`, one line: `le_total` with the refuted side resolved away |
| a convoy `match leb(x, h) as λ b => (leb(x, h) = b) -> …` applied to `refl`, then `trans` of two congruences | `match le_dec(x, h) as λ d => …`, whose motive names `or_pick`'s own scrutinee |

The proofs lost **every** `j`, **every** `trans`, and every congruence. The
reason is structural rather than lucky: a `Bool` scrutinee has to be reached by
an equation, because nothing about `b` tells the goal which branch was taken; a
decided disjunction is reached by a motive that mentions the scrutinee, so each
arm's goal has already reduced to the branch that arm picked. `le_head_insert`'s
two arms are now a hypothesis handed back unchanged, both of them.

What did *not* change: `insert` and `isort` still compute. `isort([3,1,2])` is
`refl`-provably `[1,2,3]`, which is the property the whole "a decider is a `fn`,
never a `theorem`" discipline exists to protect.

## 5. Residue

- **The equation carrier** (§3.1) — `issues/decidable-equation-carrier.md`.
- **Value-generic instances** (§3.2) — `issues/value-generic-instances.md`.
  This is the one that unblocks the relations, and therefore the one that
  matters most to `Decide`.
- **`Decide` is now the widest class in the registry**, and selection tries
  every candidate of a class in sorted order. Six instances today, each a
  checking-position elaboration per goal. Not measured — per `CLAUDE.md` this
  was not a perf round — and filed as
  `issues/resolution-candidate-fan-out.md`.
- **`Iff` has no composition instance.** Nothing wanted one yet; it is
  `And<P -> Q, Q -> P>` in content, and deciding implications is a bigger
  question than this class settled.
