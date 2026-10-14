# Rationals as the setoid round's first arithmetic client

Date: 2026-10-10. The setoid area was paused on 2026-09-05
([setoid-roadmap-and-resumption](../issues/setoid-roadmap-and-resumption.md))
until a real client asked for it. This round resumes it with the client the
roadmap's own resumption rule names "a mathematical representation already
needed elsewhere": unreduced rationals, the first step toward the real-number
probes ([regular-cauchy-reals](../issues/regular-cauchy-reals.md),
[constructive-ordered-field-interface](../issues/constructive-ordered-field-interface.md)).

- `lib/std/pos.hthr`: positive naturals, positive by construction, and
  cancellation of an `Int` factor by a `Pos`. Deleted 2026-10-14: `Rat`'s
  denominator is now `Pos<Nat>` binder sugar and the cancellation lemmas live
  in `rat.hthr` (docs/positivity-evidence-design.md §14).
- [`lib/std/rat.hthr`](../lib/std/rat.hthr): `Rat`, its equality `≈`, the
  respectful operations, and the ring, order, field and embedding laws modulo
  `≈`.
- [`docs/showcase/rat_client.hthr`](showcase/rat_client.hthr): a client that
  never looks inside a fraction.
- `crates/elab/tests/lib_std_rat.rs`: closure, the law kit by name, and the
  negative controls.

## What a client writes

```heather
theorem mul_inv_cancel(x, y: Rat, nonzero: ¬(x ≈ Rat::zero())): (y * x) * x.inv() ≈ y {
    calc {
        (y * x) * x.inv() ≈ y * (x * x.inv()) := Rat::mul_assoc(y, x, x.inv()),
        ≈ y * Rat::one() := rel_cong(Rat::mul_inv(x, nonzero)),
        ≈ y := Rat::mul_one(y),
    }
}
```

Read it as: regroup the product, replace `x · x⁻¹` by one inside the
surrounding product, and drop the one. Nothing new was needed in the language
for this. The pieces the finite-set rounds built carry over to a concrete
carrier unchanged:

- `designation ≈ at Rat := Rat::Same`, beside `+`, `*` and prefix `-`, gives
  the symbols their meaning at `Rat` only.
- `instance Equivalence<Rat>(Rat::Same)` is what `calc` uses to join `≈` steps
  (`relation_step`). It is also what `relation_step(Rat::Same, …)` resolves
  when called directly.
- `instance Respects2<Rat, Rat, Rat>(Rat::Same, …, Rat::add)` (and the one for
  `mul`) is what `rel_cong` finds when it lifts a step through `+` or `*`.
- `Semigroup` and `Commutative` from `algebra_rel` are registered for both
  operations, so generic relation-indexed clients apply at `Rat`.

## The representation

`Rat` is `{ num: Int, den: Pos }` and `Pos` is `{ pred: Nat }`, standing for
`pred + 1`. A denominator therefore cannot be zero. No proof field rides
along, so neither operations nor equality ever compare proofs. Nothing is
reduced: there is no gcd, no normal form and no non-structural recursion.

`x ≈ y` is `x.num * y.den.int() = y.num * x.den.int()`. Representation
identity stays available and is strictly finer. The showcase proves `1/2 ≈
2/4` by `refl` (cross-multiplication computes on closed fractions), and
proves `1/2 ≠ 2/4`. It also proves that no theorem can make the denominator
respect `≈`, because `2/2 ≈ 1/1`. That is setoid-core-api's "denominator
extraction must fail as an invariant observation", as a theorem.

Transitivity is the only place where the cross-multiplication equality needs
something beyond rearrangement: the middle denominator has to be cancelled.
`Int::mul_cancel_pos_r(x, y, p: Pos, h: x * p.int() = y * p.int())` does that.
Taking a `Pos` means the integral-domain side condition is discharged by the
type. The order counterpart, `Int::mul_le_cancel_pos_r`, carries `≤`
transitivity.

`inv` is total, with `0⁻¹ = 0`. The field law `x * x.inv() ≈ 1` takes
`¬(x ≈ 0)`, and the test checks that both the hypothesis-free statement and
`0 · 0⁻¹ ≈ 1` are refused. `inv_respects` covers the zero case too.

## Where the proof text went

About a third of `rat.hthr` is commutative-ring rearrangement of integer
products. That covers `cross_term` and `add_respects`, `add_assoc`,
`distr_monomial` and `mul_add_distr`, and the shuffles in `same_trans`. The
setoid layer itself is small: the equivalence, the instances and each
`*_respects` statement are a few lines each.

The pattern that kept the rearrangement tolerable was to:

1. expand both sides by distributivity;
2. prove each pair of monomials equal with `mul_assoc`, `mul_comm` and the new
   `Int::mul_shuffle` / `Int::mul_right_comm`;
3. let `omega` do the linear bookkeeping, treating each product as an atom.

`cong` by anti-unification (no written motive) carried every
"rewrite this factor" step in the `calc` chains.

## What the client exposed

Each item below has an owner.

1. **No commutative-ring normalizer** ([ring-normalization](../issues/ring-normalization.md)).
   Every law past the identity-shaped ones is a hand-written monomial match.
   Distributivity needed a seven-factor monomial lemma. Reals will multiply
   this: every Cauchy-modulus estimate is a polynomial identity or
   inequality. *Since 2026-10-12 the laws are one `ring` call each
   ([ring-normalization-design](ring-normalization-design.md)); the
   rearrangement described above is history.*
2. **`omega` does not see through a defined proposition**
   ([omega-unfolds-defined-propositions](../issues/omega-unfolds-defined-propositions.md)).
   A hypothesis `h: x <= y` at `Rat` is `Rat::Le(x, y)`, and omega skips it.
   So does a goal `x ≈ y`, and a `Pos::val(…)` atom that computes to `Succ(…)`.
   Most `omega` calls in `pos` and `rat` first restate the goal or a
   hypothesis in its unfolded form with a typed `let`. omega also
   skips a fact built as `Int::cong(λ …, p)` ("could not spell"). Those were
   rewritten as typed `cong(p)`.
3. **The elaborator accepts a hypothesis as refined by a `match` that the
   kernel then rejects**
   ([elab-match-refines-hypothesis-kernel-rejects](../issues/elab-match-refines-hypothesis-kernel-rejects.md)).
   `match n { Zero => false_elim(h(refl)) }`, with `h: ¬Is(n)` taken before
   the match, elaborates, and then fails in the kernel with a bare
   `NotConvertible`. The workaround used throughout `inv_*` is to take the
   hypothesis after the match (`→` in the statement, `λ h =>` in each arm).
4. **Sign case splits.** `inv_parts_respects` is nine sign cases, six of them
   contradictions read off two sign lemmas. A trichotomy-on-sign view of `Int`
   would shorten it. This is not filed: one site, and the ring normalizer
   would not help it.

Things that needed nothing: `calc` over `≈` and `rel_cong` at a concrete
carrier, the `prefix -` designation inside `rel_cong`'s contexts, and
instance resolution for the relation-indexed classes. The dictionary
projection cost that the finite-set client hit
([setoid-dictionary-projection-growth](../issues/setoid-dictionary-projection-growth.md))
did not appear: the whole module and the client check in about two seconds
cold.

## Not in this round

- Strict order, `abs`, multiplication monotonicity and Archimedean facts:
  [rational-order-completion](../issues/rational-order-completion.md). *Done 2026-10-14:
  [rational-order-round](rational-order-round.md).*
- Morphisms as respectful functions compared pointwise, and a function-valued
  representation: these remain [setoid-core-api](../issues/setoid-core-api.md)'s
  acceptance.
- An ordered-field interface `Rat` would instantiate:
  [constructive-ordered-field-interface](../issues/constructive-ordered-field-interface.md).
- The native-side setoid client chosen next, the x86 model's
  states-equal-except-AF relation:
  [same-defined-state-setoid](../issues/same-defined-state-setoid.md).
