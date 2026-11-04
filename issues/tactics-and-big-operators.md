---
title: Which tactics read ∑ and ∏, and how
status: closed
labels: [tactics,stdlib,mathematics]
area: tactics
milestone: [tac-arith]
created: 2026-10-27
updated: 2026-10-27
---

The range sum `MonoidRel::range(op, n, f)` (`lib/std/algebra/big_operator.hthr`,
[[finite-sums-and-products]]) and its notation `∑ k < n, e` / `∏ k < n, e`
landed with no tactic knowing about it. This round reviewed every tactic
against it: should it read a sum by its logic, and if so, how. The probes
for each judgement are in `lib/_tests/std/algebra/big_operator_tests.hthr`.

## The reading the arithmetic tactics share

A sum is an atom (one opaque value, the same atom wherever it is spelled the
same), with two exceptions, both the sum's definition and so both checked by
conversion (`crates/elab/src/range_sum.rs`):

- at the bound zero it is the operation's unit (`0` for `+`, `1` for `*`);
- at a bound that is a successor *as written* (`Succ(m)`, `m + c` at a
  numeral `c`, or a numeral up to 16) it is `range(op, m, f) ∙ f(m)`.

The second is the induction step every proof over a sum takes (`∑ k < n + 1,
f(k)` against a hypothesis about `∑ k < n, f(k)`). Every other law
(reindexing, splitting, linearity, Fubini) stays a named lemma: unfolding
further would make a tactic's reading grow with the term, and a law like
`∑ (f + g) = ∑ f + ∑ g` is not an identity of commutative rings over atoms.

## Judgement per tactic

| tactic | should it read sums | status |
|---|---|---|
| `ring` (Nat, Int, Rat, CReal, classes) | yes: atoms + the two definitional readings, at `+` and `*` | done (`ring.rs` `range_step`) |
| `linarith` | yes, through `ring`'s reader | done (inherits) |
| `omega` (Nat, Int) | yes: atoms + the two readings at `Nat::add` / `Int::add` | done (`omega_cert.rs`) |
| `positivity`'s `omega` defaults | yes | done (inherits omega) |
| `mono` | yes: `∑ f <= ∑ g` termwise, under the binder (`k < n` in scope), and `0 <= ∑ f` from termwise signs | done at Rat, CReal, Int, Nat and class carriers (`LocatedAddGroup`, `OrderedField`) |
| `mono` on `∏` | yes in principle, but monotonicity of a product needs nonnegative terms | not done; refused with the ordinary "no number of arguments" note (probe `mono_product`) |
| `norm_num` | yes, by value | already worked at Nat/Int/Rat/Dyadic by evaluation; CReal now reads a closed sum or product term by term (`norm_num_range`) |
| `intervals` | yes, on closed sums | already worked (Rat leaves compute, CReal leaves are enclosed); a term-by-term reading is not needed yet |
| equation `rewrite` under `∑` | yes | already worked: an equation rewrites under the binder |
| setoid `rewrite` / `rel_cong` under `∑` | yes | done: `rewrite` ([[rewrite-setoid-under-binders]], crossing by `MonoidRel::range_pointwise`), `rel_cong` by the same crossing ([[rel-cong-under-binders]]) |
| `split_all`, `subst`, `decide`, `bv_omega`, `rel_derive` | no: none of them has a reason to look inside a sum | no change |

## What landed besides the readings

- `mono`'s termwise laws: `Rat::range_le`, `CReal::range_le`, `Nat::range_le`,
  `Int::range_le`, the `range_nonneg` signs, and class laws through a new
  `ClassOp::Named`. `mono` now introduces a Π goal (`(k: Nat) → k < n → …`)
  and applies premised locals and given facts at a leaf, so a term bound
  given as `h: (k: Nat) → f(k) <= g(k)` closes it.
- The order lemmas are stated in call form, `MonoidRel::range(+, n, f)`, not
  `∑ k < n, f(k)`: `apply`'s matcher solves no higher-order pattern, and the
  call form converts with every spelling by η.
- The tactic view (`Head`) shows a β-redex as its contractum, as the
  diagnostics spell it; a peeled `f(m)` is one.
- Qualified spelling hides the op-index implicit a symbol slot introduces
  (`#op≈@…`), which no call can write.

## Left

- `∏` monotonicity in `mono` (nonnegative terms as side goals), filed when
  a client wants it.
- A `∑` at Nat in a module that does not import `relation` fails with a note
  that does not say the import is missing.
