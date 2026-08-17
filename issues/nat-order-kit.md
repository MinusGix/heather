---
title: "Nat's order stated in Prop: Le by recursion, Lt, and the lemma kit"
status: open
labels: [stdlib,frontend,proofs,orders]
blocked-by: [std-logic-module]
created: 2026-08-16
updated: 2026-08-16
---

`lib/std/nat.hthr` states its order as `fn Le(n, m: Nat) -> Type { leb(n)(m) =
True }` — a *reflection* of a Bool decision. Per [[class-ops-prop-vs-bool]]'s
recorded direction (2026-08-09, reaffirmed 2026-08-16), that is a v1 artifact:
the mathematical relation should be stated once, propositionally, with no
parallel Bool in the public API. This issue owns the replacement at `Nat`.

It also owns `Lt`, which does not exist at all.

## The definition: three routes, and why the choice is soft

**(a) Recursion into `Type`** — the recommendation.

```heather
fn Le(n: Nat) -> Nat -> Type {
    match n {
        Zero => λ (m: Nat) => True,
        Succ(k) => λ (m: Nat) => match m { Zero => Empty, Succ(l) => Le(k, l) },
    }
}
```

**Curried, and not by preference.** The uncurried two-argument spelling is
REFUSED — "recursive call to `Le` must pass `n` unchanged", the
[[ih-generalization]] gap — because the inner `match` makes the recursive call
vary both arguments. `leb` and `sub` in `lib/std/nat.hthr` are already curried
for exactly this reason, so the shape is the file's existing idiom rather than
a new tax, and call-site over-application means `Le(n, m)` still writes.
Verified by elaborating both spellings (2026-08-16). Falsity is `Empty` and
not `False`, per [[false-collides-with-bools-constructor]].

- Closed instances **reduce**: `Le(3, 1000)` normalises to `True`, so the
  proof is the one-node term `trivial`. That is proof-by-reflection with no
  Bool, no `decide`, and no bridge lemma — the proposition is its own
  decision procedure, and the kernel does the work by reduction rather than
  by traversing a derivation. Directly relevant to checking speed.
- Inversion is **definitional**: `h : Le(Succ k, Succ l)` *is* `h : Le(k, l)`.
  No inversion lemmas, no no-confusion machinery. Absurd cases are `Empty`.
- **Definitionally proof-irrelevant, for free.** `True` is the kernel's
  `Unit^0` ([[true-prop-trivial-hypotheses]], landed 2026-08-16), whose η rule
  makes every inhabitant convertible — so two proofs of `Le(n, m)` at closed
  arguments are *judgmentally* equal, with no squashing, no `SProp`, and no
  cost under proof relevance. This is the strongest single argument for (a)
  and it did not exist a week ago.
- Needs nothing that has not landed (large elimination is kernel v0).
- **Costs:** it is a definition that unfolds, so goals can display as `True`
  rather than `n <= m`, and conversion may unfold it where you would rather
  it did not — an ergonomic tax wanting an irreducibility control eventually.
  It does not generalise: only relations that are structurally recursive on a
  concrete inductive can be written this way, and there is no induction
  principle *on the relation* (you induct on the numbers instead — for `Nat`
  usually what you wanted).

**(b) An indexed inductive family** (`le_refl : Le(n,n)`,
`le_step : Le(n,m) -> Le(n, Succ m)`) — the uniform technique, and the one
that works for relations (a) cannot express: accessibility, transitive
closures, evaluation and IR-well-typedness relations. Those are coming
regardless, so families are not a cost this issue can avoid paying elsewhere.
Costs here specifically: inversion is not free (under the fording-over-`Wf`
route that means generated no-confusion with `sEq` indices), and proof size at
numerals is linear — `Le(3, 1000)` is 997 `le_step`s, which is exactly the
pressure that produced Lean's `decide`. Blocked on [[indexed-families]].

**(c) `exists k, add(n, k) = m`** — writable today; `le_add` in
`lib/std/nat.hthr` already half-proves the bridge. Small proofs at numerals
(`⟨k, refl⟩`), and it is the presentation that makes the *generic* ordered-
algebra layer work, since "the order comes from the addition" derives an order
on any such carrier uniformly. Costs: antisymmetry needs cancellation,
inversion needs `succ_inj`, and it only applies to carriers with the
structure.

**Why the fork is softer than it looks.** The order classes take `le` as an
**abstract field**, so the definition at `Nat` is an implementation detail
behind an instance. Take (a) as the `Nat` definition, (b) as the general
technique when families land, and prove (c) as `le_iff_exists_add` — then any
individual proof picks whichever view is shorter.

**The discipline that makes this real: downstream never unfolds `Le`.** The
API is the lemma kit, not the definition. With that held, swapping (a) for (b)
is a body-only edit; without it, every route choice is permanent.

## `Lt`

`<=` lexes and desugars to `Le(a, b)` at the non-associative comparison rung.
**Corrected 2026-08-16, having read the parser rather than the commit log:**
`<` is on that rung too and emits the symbol `<` (`Parser::comparison`,
`op_symbol`), so the token, the rung and the non-associativity all exist
already. What is missing is only the *target*: `<`'s fallback name is `lt`,
which nothing defines, so every `a < b` fails at resolution. `Lt` is therefore
a library declaration plus a designation row, not a grammar change.

It is not decoration. Four uses, in descending order of force:

1. **Termination.** `decreases` measures ([[termination-measures]]), `Acc`,
   well-founded recursion — all stated on strict decrease. `div`, `mod`,
   `gcd`, merge sort and the idealized parser are downstream of `<`.
2. **Bounds, and the guarded-total story.** `nth_lt(xs, i, h: i < len(xs))` is
   the canonical guarded total function of [[guarded-to-option-adapter]], and
   [[surface-fin-indexing]]'s `Fin(n)` *is* `i < n`. `Lt` is upstream of that
   work, not beside it.
3. Trichotomy, `lt_of_le_of_ne`, and antisymmetry statements.
4. Strict monotonicity (`add_lt_add_l`, `mul_lt_mul_l`) for anything measured.

Definition at `Nat`: `Lt(n, m) := Le(Succ(n), m)`. One line, computes under
(a), and `lt_succ_iff_le` is `refl`. In the class it is a **field**, not a
definition — see [[strict-order-presentation]].

Notation: `<` at the existing comparison rung, non-associative like `<=`. Hold
`>` and `>=` back until a use site asks, per the argument-flip caution the
receiver-position work established.

## The kit

Order: `le_trans`, `le_antisym`, `le_total` (`n <= m ∨ m <= n`), `zero_le`,
`not_succ_le_zero`, `le_succ_succ` and its inverse, `le_succ_r` (exists),
`le_refl` (exists).

Strict: `lt_irrefl`, `lt_trans`, `le_of_lt`, `lt_of_le_of_ne`, `lt_succ_self`,
trichotomy.

Bridge: `le_iff_exists_add` (route (c) above; `le_add` is most of it).

Arithmetic interaction: `add_le_mono`, `mul_le_mono`, `le_of_add_le_add_l`,
and the `sub` kit that `sub_zero` currently stands alone in —
`add_sub_cancel`, `sub_add_cancel` (under `n <= m`), `sub_self`, `sub_le`.

Then `min`/`max`, which at `Nat` are plain structural recursions needing no
decision at all (`min(0,m)=0`, `min(Sk,0)=0`, `min(Sk,Sl)=S(min(k,l))`) — a
small standing correction to the assumption that a "decided" function needs a
decider.

## Migration

`Le`'s definition changes under existing consumers. `lib/std/algebra.hthr`'s
`Cmp<Nat>` instance, `lib/list_algos.hthr`'s `sortedb`/`insert` kit and
`lib/ir_v1.hthr`'s bounds uses all state things in the reflected form; the
restatement cost is itself the measurement [[decide-class]] wants, so run it
deliberately rather than incidentally.

## What it assumes from elsewhere

- **[[std-logic-module]]** owns `Empty`/`Or`/`Not` and the `∨`/`¬`/`∃`/`∀`
  spellings. **Landed 2026-08-16**, so this is a dependency met rather than
  pending. `True` comes from [[true-prop-trivial-hypotheses]] instead and is
  already in scope.
- **[[class-ops-prop-vs-bool]]** owns the Prop-vs-Bool direction. Assumed
  here: only that the public relation is propositional and no parallel `leb`
  is part of the API.
- **[[strict-order-presentation]]** owns whether the class carries one
  relation or two. Assumed here: only that `Nat`'s `Lt` must exist either way.
- **[[indexed-families]]** owns declared families. Assumed here: only that
  route (b) is unavailable until they land.
- **[[decide-class]]** owns branching on a proposition. Assumed here: only
  that `le_dec` is a five-line structural recursion under definition (a).

## Log

- 2026-08-16: Filed out of the std-API design discussion, which reversed the
  Bool-first framing this file's current `Le` came from. The finding worth
  keeping: definition (a) gets proof-by-reflection *for free* — the thing the
  `= True` idiom exists to buy in Lean — because the proposition reduces to
  `Unit` at closed arguments. That, plus definitional inversion, is why the
  recommendation is (a) rather than the Lean-shaped (b).
