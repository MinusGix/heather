# Regular Cauchy reals on dyadic terms at the binary rate

Date: 2026-10-30. Closes
[creal-dyadic-binary-rate](../../issues/creal-dyadic-binary-rate.md). The
representation is in [`lib/std/num/creal.hthr`](../../lib/std/num/creal.hthr). Its
clients are the interval enclosures
([`creal_interval.hthr`](../../lib/std/num/float/creal_interval.hthr)), the series
([`series.hthr`](../../lib/std/num/float/series.hthr)), `norm_num` at `CReal`
([`norm_num_real.hthr`](../../lib/std/tactic/norm_num_real.hthr),
[`norm_num.hthr`](../../lib/std/tactic/norm_num.hthr)) and `intervals`
([`interval_tactic.hthr`](../../lib/std/tactic/interval_tactic.hthr)). The probes
live in [`lib/_tests/std/num/creal_tests.hthr`](../../lib/_tests/std/num/creal_tests.hthr).

```heather
record CReal {
    seq: Nat → Dyadic,
    regular: (m, n: Nat) → (seq(m).rat() - seq(n).rat()).abs() <= Rat::inv_pow2(m) + Rat::inv_pow2(n),
}

fn CReal::rounded(f: Nat → Rat, reg: …f's terms within 2^-(m+1) + 2^-(n+1)…) → CReal {
    CReal(λ n => Dyadic::floor_rat(f(n), n + 1), λ m n => CReal::rounded_regular(f, reg, m, n))
}

theorem third_64(): CReal::ofRat(Rat(OfNat(1), 3)).seq(64) = Dyadic(OfNat(12297829382473034410), -65) { refl }
```

## Why

Before this round, the n-th term was an unreduced rational within 1/(n+1).
That made precision cost grow in two ways:

- **Index growth.** k bits meant asking for term 2^k. Indices also multiplied
  as expressions nested: a sum read 2n+1, and a product read (l+1)(2n+2), with
  l taken from the unreduced numerator of x_0.
- **Size growth.** Every sum and product multiplied denominators, so a term's
  size grew with the expression's depth.

Correctly rounded `exp` and `log` need 60+ bits, which is out of reach under
both.

## The representation

The n-th term is a `Dyadic` within 2^-n, so **the index counts bits**:

| operation | reads its arguments at | then |
|---|---|---|
| `x + y` | n + 1 | exact dyadic sum |
| `-x` | n | exact |
| `x * y` | n + 2 + β, β the bit width of the larger canonical bound | rounded |
| `x⁻¹` | past the gap's start, and n + 1 + w out (w the bit width of (k+1)²) | rounded |
| `ofRat(q)` | none | rounded |
| `lim xs` | `xs(n+1).seq(n+1)` | none |

`rounded` floors an exact rational term to n+1 bits. Half the rate pays for
the rounding, so a term's size stays about n + β bits however deep the
expression is. The 64-bit term of 1/3 above is computed by kernel evaluation,
and so is the 64-bit term of 1/3 · 1/3 (its mantissa is in `ninth_64`).

**Proofs stay rational.** `x.at(n)` is `x.seq(n).rat()`, and every estimate
is the rationals' lemma library read through `Dyadic::rat`. No proof does
dyadic arithmetic. The binary helpers are new in `rat.hthr`:

- `Rat::inv_pow2`, `inv_pow2_half` and `inv_pow2_le_inv_succ`;
- `scale_inv_pow2(b, n)`, which says 2^b · 2^-(n+b) ≈ 2^-n;
- `scale_inv_succ_le`, which lets a slack of 8 · 2^-i fit under a 1/(k+1)
  step.

The slack bookkeeping that used to be long `calc` chains is now one `linarith`
call, followed by `scale_inv_succ_le`. That is why `creal.hthr` now imports
`linarith`.

**Public statements keep their shape.** `≈`, `<`, `≤` and `Apart` are
unchanged, and so are the embedding, the class instances
(`OrderedField<CReal>`, `OrderedFieldOfInt<CReal>`) and every law's
statement. `≈` measures closeness in steps of 1/(k+1) and never mentioned the
rate. The design thread kept that eventual `Same` over Bishop's pointwise form
and made this a criterion. Three groups did move to the binary rate:

- the Bishop forms (`BishopSame` and `BishopLe` at 2 · 2^-n);
- `Regular` and `Limit`;
- the term lemmas (`le_term_add` and `term_sub_le` at 2^-n).

## Enclosures are exact

`CReal::enclose(x, n)` is now `[x.seq(n) - 2^-n, x.seq(n) + 2^-n]`. Its
endpoints are dyadics, and no rounding is needed: `CReal::radius(n)` is
`Dyadic(1, -n)`. The old `enclose(n, p)` rounded a rational term outward to
p bits, which was itself a source of width. `RealExpr::enclose` and the
searches lost their p for real leaves. `intervals` reads real leaves at
`n := 32` bits by default, and each try refines the index by one bit
(previously the default was index 1023, doubling per try).

## What changed for clients

- **`series.hthr`.** A series' real is now `CReal::rounded` over its partial
  sums, read at `start + (n + 1) + width(scale)`. The tail bound is restated
  at 2^-(n+1).
- **`Int::divmod`.** It runs on `Nat::ldiv` (long division) instead of the
  unary `Nat::div`. The 64-bit floors run out of fuel otherwise. The quotient
  and remainder lemmas are restated on `ldiv_spec`.
- **`intervals` on inverses.** An inverse reaches the tree as
  `RInv(a, x, h)` with the call's own apartness proof.
  - The tactic host's `View` lists only the arguments a call writes, and an
    inferred or named proof is not one of them. The reader used to fall back
    to a leaf there, and enclosed the inverse by its own terms.
  - That only worked because the old `ofRat(q)` had the constant terms q, so
    the inverse's term did not depend on the index it read. With the proof a
    hypothesis, that index is stuck.
  - The reader now recovers the proof as a hole solved against the node
    (`interval_proof_arg`, the same move `norm_num` already made).
- **`norm_num` leaves.** These are now read without terms. The old reader
  took q back from a term, which only worked because `ofRat`'s terms were q.
  The new one solves a hole `?q` by comparing the leaf with
  `CReal::ofRat(?q)`.
  - A named constant such as `third()` is not that call until it unfolds.
  - The elaborator's unifier pairs rigid spines only when their heads agree.
  - So the tactic host's comparison with holes now retries over the committed
    side's δ/β reducts, one step at a time and at most 16
    (`Unfold::HoleComparison` in `crates/elab/src/oracle.rs`). It never takes the
    weak head normal form, which would unfold `ofRat` too.
  - This is a failure-path retry: a comparison that already succeeds is not
    affected.
- **`norm_num` inverses.** The embedding's inverse now carries the embedding's
  own apartness through `CReal::inv_respects` (`inv_sound`).

## Consequence worth knowing: an inverse depends on its proof up to `=`

`x.inv(h)` reads x at an index computed from the gap that h names. Two proofs
of `x.Apart(0)` can name different gaps, which gives two inverses that are
`≈` but not `=`. That was always so in principle. It was invisible while the
embedded rationals had constant terms, because then the index did not matter.

Now a statement whose `⁻¹` is filled by the search, proved with a generic
theorem's inverse, needs `CReal::inv_respects` to bridge the two proofs. The
ordered-field showcase's `creal_archimedean_inv` shows the pattern.
`inv_respects` takes both proofs as defaulted parameters, so the bridge is
one call.

## Tests

- The creal probes are restated at the binary rate, with new evaluated values:
  - the termwise indices (sum n+1, product by bit width, inverse past the
    gap, limit n+1);
  - the moduli and gaps (`gap_size` 7, `squared` 255);
  - the 64-bit terms;
  - Bishop's identity sequence, which is now not regular at the binary rate.
- `creal_interval_tests` checks exact enclosures: `third_at_10` is
  [680/2048, 684/2048].
- In `interval_tactic_real_tests`, the inverse goals pass through `RInv`,
  including `inv_open_proof`, where the proof is a hypothesis. The refinement
  probes start at index 3.
- `norm_num_real_tests` passes unchanged.
- In `crates/elab/tests/lib_std_creal.rs`, the termwise vacuity controls and
  the strengthened Bishop bound are now refused by the elaborator, as
  mismatches, instead of by the kernel. They compare dyadic terms read as
  rationals, which the elaborator now compares itself.

## Left out

- `Interval::span` is no longer used by `CReal::enclose`. It stays as a
  general rounding constructor.
- Correctly rounded `exp` and `log` (the `float-reals` and
  `float-transcendental` milestones in [the roadmap](../roadmap.md)) were blocked
  on this round, and are not part of it.
