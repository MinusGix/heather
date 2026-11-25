# P3109 formats in the float library: design

Status: design, 2026-11-25. Owns the roadmap milestone `float-p3109` and its
submilestones `p3109-values`, `p3109-projection` and `p3109-encoding`
(`docs/roadmap.md`); tracking issue
[float-p3109](../../issues/float-p3109.md). It extends
`docs/library/floating-point-design.md` (below, "the float design") and
changes only what P3109 needs; everything else there stands.

Sources. The IEEE P3109 *Interim Report* v4.1 (14 September 2026, the
working group's public repository `github.com/P3109/Public`, file
`IEEE P3109 Interim Report.pdf`; §3.1 formats, §4.7 the auxiliary
operations), its value tables (`Value Tables/Hexadecimal/K*/P*/…csv`, every
code point of every format for `K = 3 … 16`), and the FLoPS paper
(`docs/papers/2602.15965v3.pdf`), a Lean formalization of an earlier draft.
Section numbers `R§…` below are the report's.

## 1. What P3109 is, in the library's terms

A format is `Binary{K, P, Σ, Δ}`: bitwidth `K > 2`, precision `0 < P < K`
(signed) or `0 < P <= K` (unsigned), signedness, and a `Finite` or
`Extended` domain (R§3.1). The bias is `B = 2^(K-P-1)` signed and
`B = 2^(K-P)` unsigned. Decoding (R§4.7.2) is IEEE's with the special
values moved:

| | NaN | `+∞` | `-∞` |
|---|---|---|---|
| signed extended | `2^(K-1)` | `2^(K-1) - 1` | `2^K - 1` |
| signed finite | `2^(K-1)` | – | – |
| unsigned extended | `2^K - 1` | `2^K - 2` | – |
| unsigned finite | `2^K - 1` | – | – |

Every other code `x` of the nonnegative half is `T = x mod 2^(P-1)`,
`E = x ÷ 2^(P-1)`, value `T·2^(1-P)·2^(1-B)` when `E = 0` and
`(1 + T·2^(1-P))·2^(E-B)` otherwise; a signed format's negative half is the
mirror. So the datum set is IEEE-shaped below the top, and the top is cut
short by the codes the specials take. There is one zero and one NaN: the
datum set is a subset of the *closed extended reals*
`R ∪ {-∞, +∞, NaN}` (R§3.1 note 1), which has no `-0`.

Operations decode, compute exactly over the closed extended reals, and
**project**: round to precision with unbounded exponent (R§4.7.4), then
saturate (R§4.7.5), then encode. Rounding modes are IEEE's five plus
`ToOdd` and three stochastic variants; saturation is `SatFinite`,
`SatPropagate` or `SatNone`, chosen per operation.

## 2. Decisions

### D1. A P3109 datum is a `Float(F)` up to value sameness

`Finite(F)` keeps its sign bit, and with it `-0`. P3109 never observes the
sign of zero: its data are values, and the library already has the
relation for that (`≈`, value sameness, which identifies the zeros). So a
P3109 datum is a `Float(F)` read up to `≈`, the encoding sends both zeros to
code 0, and decoding produces `+0`. Every theorem stated at `≈` (all the
rounding, error and EFT theorems) means the same at a P3109 format; the
IEEE sign-of-zero theorems are true and irrelevant there.

Rejected: a format flag that forbids `neg ∧ mag = 0` in canonical form.
Then `Finite::neg` stops being "flip the sign bit" (it must not flip a
zero), `-(-x) = x` loses its one-line proof, and every sign-flip lemma in
`round.hthr`, `eft.hthr` and `interval.hthr` (they reduce the negative case
to the positive one through `-`) needs a case on zero, to buy a
distinction P3109 does not make.

### D2. An unsigned format is the nonnegative half of a signed envelope

The unsigned datum set is exactly the nonnegative half of a signed format
with the same `frac`, `emin`, top binade and specials (§3 builds it), so
`Format::p3109(K, P, Unsigned, Δ)` *is* that envelope, and "unsigned"
lives in two places only:

- **projection** (`p3109-projection`): rounding is sign-symmetric, so an
  unsigned projection is the envelope's rounding followed by R§4.7.5's
  rules for a negative result (`Mlo = 0`): `SatFinite` and `SatPropagate`
  give `0`; `SatNone` gives `0` under `TowardZero` and `TowardPositive`
  and `NaN` otherwise;
- **encoding** (`p3109-encoding`): the codes cover the nonnegative data,
  and `-∞` has none.

Rejected: an `Unsigned` flag in canonical form. `Finite::neg` would be
partial, and every theorem whose proof reduces `x < 0` to `-x > 0` would
need a signedness hypothesis.

### D3. `Format` gains a reserved count and loses `1 <= frac`

```heather
record Format {
    frac: Nat,                                // precision frac + 1, now >= 1
    emin: Int,
    span: Nat,                                // binades above emin that hold finite values
    cut: Nat,                                 // largest significands the top binade gives up
    cut_ok: cut + 1 <= Nat::pow(2, frac),     // the top binade keeps its least normal significand
    specials: Specials,                       // Ieee, NanOnly or FiniteOnly: which specials exist
}
```

- `frac_ok` goes: precision one is `frac = 0` (R§3.1 allows `P = 1`).
  `half = 1`, `top = 2`: every nonzero finite value is `±2^e`, and there
  are no subnormals (the least value `1 · 2^qmin` is normal), which is what
  the tables show.
- `cut` replaces `Specials::reserves_top: Bool`. The top binade holds
  significands `half … top - 1 - cut`; E4M3 is `cut = 1` (its NaN), every
  IEEE format `cut = 0`. `Specials` keeps only what it says: whether there
  are infinities and NaN. `NanOnly` no longer implies a reservation, and an
  extended P3109 format has infinities *and* `cut > 0`, which the old
  `Specials::inf_free` (only formats without infinities reserve) forbade.
- `cut_ok` keeps the top binade nonempty, so `max_mag = top - 1 - cut >=
  half`, and `span` really is the exponent of the largest finite value.
  A reservation that empties a binade is expressed by a smaller `span`, as
  §3 does. That keeps `max_finite`, `limit_h` and the cell search exactly
  as they are.

**Why the reserved count is the right parameter.** FLoPS (§3.1, Figure 3)
needed a five-way case split for P3109's `emax`, and the interim report had
it wrong for unsigned formats with `P <= 2` (FLoPS §6). Here `emax` is not
tabulated: §3 derives `span` and `cut` from the number `R` of codes the
specials take at the top of the nonnegative half, by one division. At
`P = 1` a binade is one code, so each reserved code removes a binade; at
`P = 2` two codes remove one; above that the binade only shrinks. The
report's `emax` table is a theorem about §3's function (`p3109-values`
checks it against the value tables by evaluation).

### D4. Ties go to the code that is even

R§4.7.4 breaks a nearest-even tie toward `CodeIsEven`: `IsEven(⌊S̃⌋)` when
`P > 1`, and `⌊S̃⌋ = 0 ∨ IsEven(Q + B)` when `P = 1`. Both say that the
*code point* of the candidate ends in 0. For `P > 1` the code's last bit is
the significand's (the hidden bit sits above `half`, which is even). For
`P = 1` there are no trailing bits and the code is the biased exponent;
in the library's terms, the float `1 · 2^(qmin + b)` has code `b + 1`.
So:

```heather
// The last bit of the float's code: the significand's when there are
// fraction bits, the biased exponent's when there are none.
fn Format::lsb(self F: Format, mag, bexp: Nat) → Nat { match F.frac { Zero => mag * Succ(bexp), Succ(_) => mag } }
fn Finite::Even({F: Format}, self f: Finite(F)) → Type { Nat::Even(F.lsb(f.mag, f.bexp)) }
```

and `Finite::NearestEven` says `Finite::Even(f)` where it said
`Nat::Even(f.mag)`. At `frac >= 1` that is the same proposition by
computation, so the IEEE formats' theorems do not move. The old rule has no
witness at `P = 1`: a tie between `2^e` and `2^(e+1)` has `mag = 1` on both
sides. Two neighbours always have codes one apart, so exactly one is even;
that is the fact `near_tie_ok` uses, and at `frac = 0` it is the parity of
consecutive exponents.

### D5. The nearest-even overflow tie follows the largest float's parity

Rounding to precision before saturating (R§4.7.3, note 1) means a nearest
mode overflows from the midpoint between the largest finite value `Mhi` and
the next grid value above it, `ovf = Mhi + ulp/2`. Below `ovf` the result is
`Mhi`; above it, overflow. *At* `ovf`, ties to away overflow, and ties to
even overflow exactly when `Mhi`'s code is odd. IEEE's formats all have an
odd `Mhi` (`top - 1`), which is why the library could say `ovf <= x`. A
signed extended P3109 format has `Mhi = top - 2` (its `+∞` takes the top
code), even: `Binary8p3se`'s tie at `ovf` rounds to `Mhi`.

```heather
fn Format::ovf_h(self F: Format) → Nat { (F.max_mag() + F.max_mag() + 1) * Nat::pow(2, F.span) }
// A tie at `ovf` stays at the largest float: ties to even, and an even largest float.
fn Format::TieStays(self F: Format, even: Bool) → Type { even.IsTrue() ∧ F.MaxEven() }
fn Format::Fits(self F: Format, even: Bool, x: Rat) → Type {
    F.specials.has_inf().IsTrue() → x.abs() < F.ovf() ∨ (F.TieStays(even) ∧ x.abs() ≈ F.ovf())
}
fn Format::Over(self F: Format, even: Bool, x: Rat) → Type { F.ovf() <= x ∧ (F.TieStays(even) → F.ovf() < x) }
fn Format::Under(self F: Format, even: Bool, x: Rat) → Type { x <= -F.ovf() ∧ (F.TieStays(even) → x < -F.ovf()) }
```

`RoundsTo`'s nearest clauses use `Fits(even, x)` for a finite result and
`Over(even, x)` or `Under(even, x)` for an infinite one. `ovf_h` is
written through `max_mag`, which is `top - 1` for an IEEE format, so the
threshold is unchanged there. The rounding routine (`none_h`) gets the
tie: it already knows `h` and the sticky bit, so `h = ovf_h` with no sticky
bit is the tie.

### D6. Saturation and the new modes are the projection round's

Saturation becomes a parameter in `p3109-projection`
([float-saturation-modes](../../issues/float-saturation-modes.md)): today's
`RoundsTo` is `SatNone` at a format with infinities and `SatFinite` at one
without, which is exactly R§4.7.5 for every rational input except `SatNone`
at a finite-domain format (overflow is `NaN` there). Round-to-odd and the
stochastic modes join the mode set in that round. `p3109-values` changes no
saturation behaviour.

## 3. The P3109 formats as `Format` values

```heather
inductive Signedness { Signed, Unsigned }
inductive Domain { Finite, Extended }

fn Format::p3109(K, P: Nat, s: Signedness, d: Domain) → Format
```

with, for `half = 2^(P-1)`:

- `frac = P - 1`, `B` as in §1, `emin = 1 - B`;
- `C` nonnegative codes (`2^(K-1)` signed, `2^K` unsigned) and `R` of them
  reserved at the top (signed: 0 finite, 1 extended; unsigned: 1 finite, 2
  extended), so the largest finite code is `n = C - 1 - R`;
- `span = n ÷ half - 1` (the code's biased exponent, less one: the
  library's `bexp` counts binades above `emin`, and IEEE's `E = 1` is
  `bexp = 0`);
- `cut = half - 1 - n mod half` (the top binade's significands are
  `half … half + n mod half`);
- `specials = Ieee` for an extended domain and `NanOnly` for a finite one.

`cut_ok` holds by construction. `n ÷ half >= 1` (the largest finite value is
normal) holds for every valid `(K, P)` with `K >= 3`; the constructor takes
the parameters' validity (`3 <= K`, `1 <= P`, `P < K` or `P <= K`) as an
`IsTrue` proof, so a literal format closes it by `trivial`. The named
8-bit formats (`binary8p1se` … `binary8p7uf` as needed) are literal
applications, and their constants close by evaluation.

Checked against the tables (by hand, here; by evaluation in the tests):

| format | `B` | `n` | `span` | `cut` | `Mhi` |
|---|---|---|---|---|---|
| `Binary3p1se` | 2 | 2 | 1 | 0 | `1` |
| `Binary3p2se` | 1 | 2 | 0 | 1 | `1` (`mag 2`, even) |
| `Binary3p2uf` | 2 | 6 | 2 | 1 | `2` |
| `Binary3p1ue` | 4 | 5 | 4 | 0 | `2` |
| `Binary8p3se` | 16 | 126 | 30 | 1 | `0x1.8p+15` (`mag 6`, even) |
| `Binary8p4sf` | 8 | 127 | 14 | 0 | `0x1.ep+7` |

## 4. Rounds

1. **`p3109-values`** (this round): D3–D5 in `float.hthr` and `round.hthr`
   and their fallout (`error`, `window`, `literal`, `round_real`), §3's
   constructor, and tests: the table rows above, ties at `P = 1` of both
   exponent parities, the zero tie, the overflow tie at an even `Mhi`, and
   a negative control showing the significand-parity rule has no witness
   at `P = 1`. Issue [float-precision-one](../../issues/float-precision-one.md).
2. **`p3109-projection`**: saturation as a parameter, `ToOdd`, the
   stochastic variants pointwise, the unsigned projection (D2), Fast2Sum's
   saturated overflow error.
3. **`p3109-encoding`**: `decode`/`encode` over `BitVec(K)` for every
   P3109 format, the bijection, and the value tables as evaluation tests.

## 5. Round 1 as landed (`p3109-values`, 2026-11-25)

Modules: `float.hthr` (D3, D4's `lsb`), `round.hthr` (D4's ties, D5),
`window.hthr`, `literal.hthr`, `error.hthr`, `round_real.hthr` (fallout),
the new `p3109.hthr` (§3), and `Nat::even_add_even` in `nat.hthr`. Tests:
`lib/_tests/std/num/float/p3109_tests.hthr` (the table rows, both tie
parities at precision one, the zero tie, the overflow tie both ways, a
negative control) and two saturated Fast2Sum cases in `eft_tests.hthr`.

**As designed.** D3: `Format { frac, emin, span, cut, cut_ok, specials }`;
`Format::cut_room` is `cut_ok`, `one_le_half`/`two_le_top` replace the
bounds `frac_ok` gave, and `two_le_half` now takes `1 <= frac`.
`max_mag = top - 1 - cut` and `max_mag_bounds` is three facts, not four.
D4: `Format::lsb_at(frac, mag, bexp)` (a helper over plain naturals, so
`lsb_cases` can split on `frac` with a motive), `Finite::Even`, and two
parity lemmas the step-up record uses: `lsb_step` (a step inside a binade
moves the code by one) and `lsb_carry` (the carry into the next binade flips
it). `UpIs` states its parity facts about codes; `NearSplit` and
`nearest_even_same` read `Finite::Even`. D5: `Format::TieStays(even)`,
`Fits(even, x)` (strictly below the threshold, or on it when the tie stays),
`Over(even, x)` / `Under(even, x)` (the old `ovf <= x` as `.left`, strict
when the tie stays), and `none_h(h, st, even)` with the tie branch.
`ovf_h` is `(2·max_mag + 1)·2^span`, the old value at `cut = 0`.

**Found while landing.**

- *A window breaks precision-one ties.* A window lowers exponents by `j`,
  and at precision one the code's parity is the exponent's, so an odd `j`
  flips which neighbour is even. `Format::widen` now uses the window's
  answer only when `Format::win_par(j)` (`1 <= frac ∨ Even(j)`) holds,
  and returns the full rounding otherwise; `window_rounds_fin` and
  `window_rounds_inf` take that fact, and `win_max_even` carries the
  largest float's parity between the top window and `F` (for D5). Precision
  one formats are at most 16 bits wide, so the fallback costs nothing that
  matters; the window exists for binary64.
- *`γ` needs `u < 1`.* For a directed mode at precision one `u = 1`, so
  `u <= γ(1) = u/(1 - u)` is meaningless; `Format::u_le_gamma` takes
  `1 < u_den(mode)`, which every caller already had (`n < u_den`).
- *`rounds_beyond` needs a strict threshold.* At `ovf` itself a staying tie
  rounds finite while a larger value overflows, so the hypothesis is now
  `ovf < y`; its one caller's `y` was strictly past anyway.
- *Value-same floats have one code parity* (`Finite::even_of_same_val`,
  from `parts_of_same_val`, which now gives the exponent as well as the
  significand).

**Deviation.** `Format::p3109` takes no validity proof: it is total, and
`cut_ok` holds for any parameters. It is P3109's format exactly when
`(K, P, s)` is valid (§3); the named formats are checked against the
tables by evaluation. A `Domain`'s constructors are `FiniteDomain` and
`ExtendedDomain`, since `Finite` is the finite-float type.

**Proof-pattern observations.**

- A `match` on a `Bool` refines the goal but not the types of hypotheses
  that mention it; a lemma generic in `even` that passes `fits: F.Fits(even,
  x)` into one branch needs `match even as λ e => F.Fits(e, x) → … { … }(fits)`.
- A constant `as` motive stops the goal's own `match` on the same scrutinee
  from reducing (`none_h_sign`); leave the motive to inference there.
- A `let` bound to a lambda whose branches return different matches needs
  its type written (`inf_or` in `none_ok`).

## 6. Round 2 as landed (`p3109-projection`, 2026-11-25)

Module: `lib/std/num/float/project.hthr`, plus `Finite::fast_two_sum_sat`
at the end of `eft.hthr`. Tests: `lib/_tests/std/num/float/project_tests.hthr`
and the saturated Fast2Sum cases in `eft_tests.hthr`.

**Saturation beside `RoundsTo`, not inside it.** `RoundsTo` stays what it
was: `SatNone` at a format with infinities, `SatFinite` at one without.
The projection is stated next to it:

- `OverUp(mode, x)` / `OverDown(mode, x)`: rounding to precision leaves the
  finite range. They are literally `RoundsTo`'s infinite clauses
  (`inf_over_up`, `over_up_rounds` and their mirrors), so at a format with
  infinities they are exactly where `RoundsTo` overflows, and every
  existing overflow lemma is about them.
- `sat_up(sat)` / `sat_down(sat)`: report §4.7.5 for a finite input. The
  extreme finite float for `SatFinite` and `SatPropagate`. For `SatNone`,
  the infinity where there is one, else NaN. A format with neither (OCP
  FP6/FP4) saturates.
- `project(mode, sat, x)` decides the two, else `round_rat`; `Projects` is
  the relation and `project_correct` the bridge. `project_in_range` is
  FLoPS's Lemma 4 (inside `[-max, max]` the projection is the rounding, by
  computation), `project_none` says `SatNone` at a format with infinities is
  a correct rounding everywhere, and `project_faithful` is FLoPS's Lemma 5
  (a finite projection is the greatest float below or the least above, the
  saturated ends included).

Rejected: a saturation argument on `RoundsTo`. Every theorem about it
would have grown a case, for a distinction only the range's edges see.

**Unsigned (D2).** `project_unsigned` projects in the envelope and sends a
negative result to `unsigned_low(mode, sat)`: zero under the saturating
modes, and under `SatNone` zero toward zero or upward and NaN otherwise
(`Mlo = 0`). `project_unsigned_nonneg`: the result is never negative and
never `-∞`.

**Round to odd** (`round_odd`): truncate, and step away from zero when
that was inexact and landed on an even code; `round_odd_faithful`. It is a
function beside `Mode`, not a `Mode` constructor, for the same reason as
saturation. What is not yet proved: "an even result is exact" inside the
range, and the double-rounding theorem; the tests pin the saturation
caveat (E4M3 returns its even largest float for 460, inexactly).

**Stochastic rounding** (`round_sr_a`, `_b`, `_c`): P3109's three
`RoundAway` rules. `ν·2^N` is computed exactly from the truncation `d` as
`(|x| - |d|)·2^(N - q(d))`, which needs no case for subnormals or precision
one because `d`'s quantum is the spacing above it. Each draw goes through
`round_dir` and is faithful. `Nat::count_away_all` is the count the
expectations rest on: at `⌊ν·2^N⌋ = k`, exactly `k` of the `2^N` draws step
away under variant A.

**Fast2Sum** (`fast_two_sum_sat`, FLoPS Theorem 12): positive `b <= a`
whose sum reaches the largest float `M`, with the sum saturated to `M` by
any mode. Then `M - a` is a Sterbenz difference and `b - (M - a)` lies on
`b`'s grid between 0 and `b`, so both subtractions are exact in any
modes. The negative side is the mirror and is not stated separately.

**Observations.**

- `Fin(f)` in a type position resolves to the index type `Fin(n)`; inside a
  motive write `Float::Fin(f)`.
- A nested `match` whose result is the body of a function in the goal
  (`project_correct`) needs the motive spelled out; one level works by
  inference.
- `omega` cannot read the literal a reduced motive leaves in the goal
  (`count_away_eq`); a typed `let` restating the goal fixes it.

