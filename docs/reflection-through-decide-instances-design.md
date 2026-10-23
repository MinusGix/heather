# Reflection through `Decide` instances: the instance is the procedure

`issues/reflection-through-decide-instances.md` owns this round. Companion
records: `docs/decide-class-design.md` (the class), `docs/traits-layer2-design.md`
(resolution, whose §3.1 this amends), `docs/goal-combinators.md` (the `decide`
leaf beside `split_all`/`all_goals`).

## 1. One notion at the proof site

A closed fact whose natural spelling is too large to reduce — an unsigned
comparison at machine width, say — is discharged by running a decision
procedure and letting the kernel check the run. The objection the issue was
filed against is that this introduces a second notion: proofs want to say
`unsigned_lt`, and reflection seems to make them say `unsigned_lt_bit`.

The answer is that the specification stays the notion and the **`Decide`
instance is where the procedure is chosen**:

```heather
fn unsigned_lt(n: Nat, a, b: BitVec(n)) → Type { toNat(n, a) < toNat(n, b) }   // unchanged

fn unsigned_lt_dec(n: Nat, a, b: BitVec(n)) → unsigned_lt(n, a, b) ∨ ¬unsigned_lt(n, a, b) {
    match unsigned_lt_bit(n, a, b) as λ c => (unsigned_lt_bit(n, a, b) = c) → … {
        True  => λ h => Inl(borrow_sub_bit_true_iff(n, a, b).mp(h)),
        False => λ h => Inr(λ p => absurd(trans(sym(h), borrow_sub_bit_true_iff(n, a, b).mpr(p)))),
    }(refl)
}
instance(n: Nat, a, b: BitVec(n)) Decide<unsigned_lt(n, a, b)> { dec := unsigned_lt_dec(n, a, b) }

theorem boundary(): unsigned_lt(64, ofNat(64, 0), ofNat(64, 9223372036854775808)) { decide }
```

`lib/std/bitvec/bitvec.hthr` declares this for `unsigned_lt`, `unsigned_le`,
`signed_lt` and `signed_le`. The unsigned pair runs the ripple borrow and
transports through the iff the executable-carry round had already proved; the
signed pair runs `int::le_dec` over `toInt`, which has been one synchronous
descent since `int::add`/`sub` became payload operations
(`issues/int-arithmetic-over-nat-primitives.md`) — a bridge from
`signed_lt_bit` to `signed_lt` would buy nothing for cost and is not owed. The
executable bits themselves appear nowhere but inside the instance, and
registering a faster decision later is a library change with no proof churn.

## 2. What the probes changed about the plan

The issue was filed before the Nat run classes
(`issues/nat-run-algebra-primitives.md`), and two of its premises had expired
by the time the round ran. Measured on the release checker over the standard
library, one probe file per fact:

- **The derived decision is already cheap at literals.** `nat::le_dec` is a
  synchronous fold, so `Decide<Le(n, m)>` at two width-64 `ofNat` literals —
  reached from `unsigned_lt(64, …)` by unfolding — checks at the cost of
  loading the library. The width-64 boundary facts the issue's acceptance
  names needed no new instance to be discharged.
- **Over computed operands the cost is not the decision, it is the search.**
  At `unsigned_lt(64, ripple_add(…), ripple_add(…))` the same route exhausted
  gigabytes, while the executable bit over the same operands, and even
  `nat::le_dec` over their `toNat`s written as terms, stayed at the library's
  own footprint. What paid was **unification of a candidate whose head differs
  from the goal's**: `Le(?n, ?m)` against `unsigned_lt(64, A, B)` unfolds the
  goal and reduces the operands inside the elaborator's conversion, and every
  such candidate pays, whether it goes on to win (the `Le` instance) or to be
  rejected (`signed_le::Decide` tried before `unsigned_lt::Decide`). A
  candidate keyed at the goal's own head unifies syntactically and costs
  nothing. The type-level reduction this exposes is filed on its own as
  `issues/type-level-reduction-over-computed-operands.md`; the shape claim
  here is only that the head-keyed instance is the one that must be built
  first.

So the instances earn their place for a different reason than the issue
gave: not because the derived procedure is slow, but because the derived
*candidate* is reached by unfolding, and unfolding is where the cost lives
when the operands are computed. That made instance ordering the load-bearing
part of the round rather than a refinement.

## 3. Candidate order: the goal's own head first

Resolution selects by trial in canonical-name order (layer 2 §3.1) and §3.1
argued against head-keyed *matching* because a lowered goal does not expose
its carrier. Both stand. What is added is an **ordering** read from where the
carrier is still visible:

- A solver parameter's carrier is its written type's argument — `Decide<P>`
  — and at a call site `P` is a type parameter the application has already
  applied as a term, or an applied former written out (`Decide<Le(n, m)>`).
  `Elaborator::solver_carrier_head` (`crates/elab/src/traits.rs`) reads the
  head off that: the application built so far travels on the obligation
  (`ResolveOb::applied`), its leading arguments are the type arguments, and
  the chosen one's spine head is a global the current Ψ names. The written
  applied form resolves as an instance head does at declaration.
- `Traits::candidates(class, prefer)` puts the instances registered at that
  head first, in canonical order, then the rest in canonical order. A trace
  line `head:` records what was read. Where nothing can be read — a
  dispatch-site goal, a bare carrier that is not one identifier — the order is
  the plain one and nothing that resolved before changes.
- The preference travels into the canonical-derivation mint
  (`record_derived` → `mint_one`), which re-runs the search in the empty
  context; without that the mint would pay the general candidates a second
  time, which is exactly what the first probe with the instances in place
  showed.
- The canonical-derivation table is keyed by conversion (layer 2 §9.2), and
  that lookup was the last place the cost hid: a module's second closed fact
  at `unsigned_lt` compared its goal against the first's minted entry, and
  finding `ofNat(64, 2^63)` and `ripple_add(64, …)` *unequal* cost as much as
  the wrong candidate had. Two changes, both to an optimization and neither
  to correctness: the minted entry keeps the head (`DerivedInst::head`, in
  the image format as `HTHMOD\0\x05`) and a lookup skips an entry whose
  known head differs from the goal's; and the comparison runs under a small
  budget (`DERIVED_LOOKUP_FUEL`), an inconclusive answer counting as a miss.
  A miss costs the registry route — cheap under the head order — and a
  second mint.

An instance at the goal's head is the specific one, so this is the "more
specific instance wins" the issue asked `decidable-relations-and-comparison`
to settle, answered for the case that exists: two instances that both *fit*
a goal — `Tag<Nat>` and `Tag<Wrap(n)>` at `Tag<Wrap(3)>`, where `Wrap(3)`
unfolds to `Nat` — now resolve to the one keyed at `Wrap`, and a goal at a
head with no instance still resolves through the unfolding fit
(`crates/elab/tests/traits_resolution.rs`). Overlap *detection* is untouched:
it is still keyed on the head, and two instances at one head are still a
declaration error.

## 4. The `decide` combinator

`decide` in checking position elaborates `logic::decide_yes(refl)` at the
goal:

```heather
fn or_index<P, Q>(d: P ∨ Q) → Nat { match d { Inl(_) => 0, Inr(_) => 1 } }
theorem or_of_index_zero<P, Q>(d: P ∨ Q, h: or_index(d) = 0): P { … }
theorem decide_yes<P: Decide>(h: or_index(P.dec) = 0): P { or_of_index_zero(P.dec, h) }
```

A fixed term, as the issue asked: resolution supplies the instance, the
kernel reduces its `dec` to judge the `refl`, and nothing else is trusted.
`or_index` reads the side as a `Nat` because `Bool` is declared above
`logic`; it is a `fn` for the reason every decider is. The combinator is an
ordinary leaf, so `split_all; all_goals { decide }` works unchanged, and
`And(decide, decide)` is a term like any other.

**Shadowing.** The name is also `logic::decide`'s. A local, an alias, the
declaration's own name, or a user global called `decide` still wins; the
library's `decide<P>()` keeps its meaning where it is applied, and only a
*bare* `decide` in checking position — which was never that value, since the
value is a function — is the combinator (`Elaborator::decide_shadowed`).

**Refusal.** A false closed goal is refused by the kernel with the ordinary
`NotConvertible`, and the report is moved to the `decide` and names the
instance:

```text
the kernel rejected `wrong`: NotConvertible. `decide` resolved
`Decide<unsigned_lt(64, …)>` to `bitvec::unsigned_lt::Decide`, whose decision
here is not `Inl`: the goal is false, or not closed enough to decide
```

Every `decide` records the `or_index(inst.dec)` its `refl` claims is `0`
(`DeclAttempt::decide_uses`); only when the gate says `NotConvertible` are
those re-reduced, under the gate's own budget, and the first that converts to
the wrong side is the culprit (`Elaborator::refused_decide`). A `decide` that
decided its goal is never blamed for a `refl` beside it, and an *open* goal
that resolved — `n = n` at `Nat` — is reported in the same words, which say
"not closed enough" rather than "false". The re-reduction runs only on the
failure path, so a passing declaration pays one decision, not two.

`trivial` was not taught to fall back to `decide`: `trivial` infers `Unit^0`
and is the one bare name whose meaning does not depend on the goal, and a
closed ALU fact reading `{ decide }` says what it is.

## 5. What is left where

- `issues/resolution-candidate-fan-out.md` still owns narrowing the candidate
  *set*; this round orders it.
- `issues/type-level-reduction-over-computed-operands.md` owns the cost an
  unfolding unification pays over computed operands, which this round routes
  around and does not fix.
- `signed_lt_bit`'s correspondence with `signed_lt` is not proved and is not
  needed for cost; it remains a statement `x86` semantics may want for its
  own reasons, and is not filed here.
