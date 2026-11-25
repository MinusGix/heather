---
title: The IEEE P3109 formats in the float library
status: open
labels: [mathematics,floating-point,design]
area: mathematics
milestone: [float-p3109]
created: 2026-11-25
updated: 2026-11-25
---

Owns the roadmap's `float-p3109` milestone and the decision on how a P3109
format becomes a `Format`. Minus put P3109 in scope on 2026-11-25, after
reading Chang, Park, Lim and Nagarakatte's FLoPS paper
(`docs/papers/2602.15965v3.pdf`, a Lean formalization of the interim P3109
report): they are relevant ML formats, and covering them makes the library
strictly more general than IEEE 754 plus OCP.

## What P3109 is (from the paper, §2; check the standard before relying on it)

A format is four parameters: bitwidth `K >= 3`, precision `P >= 1` (`P < K`
when signed, `P <= K` when unsigned), signedness, and domain (`Finite`, or
`Extended` with infinities). The exponent field is `W = K - P` bits when
signed and `K - P + 1` when unsigned; the bias is `2^(K-P-1)` signed and
`2^(K-P)` unsigned. Unlike IEEE 754:

- **One zero and one NaN.** A signed format has no `-0`; its pattern
  `2^(K-1)` is the NaN. An unsigned NaN is `2^K - 1`.
- **Infinities share the top exponent field with finite values.** Signed
  extended: `+∞ = 2^(K-1) - 1`, `-∞ = 2^K - 1`. Unsigned extended: `+∞ =
  2^K - 2`, no `-∞`. Finite domains have none.
- **So the largest finite value depends on all four parameters**
  (the paper's Figure 3). The interim report got `emax` wrong for unsigned
  formats at `P <= 2` and the unsigned-extended infinity's code wrong; the
  paper's authors found both.
- **Rounding modes** add round-to-odd and three stochastic variants to
  IEEE's five, and **saturation** (`SatFinite`, `SatInf`, `SatPropagate`)
  is chosen per operation, separately from the mode.

## How it maps onto `Format` (the design question this issue owns)

`Format` today is `{ frac, frac_ok: 1 <= frac, emin, span, specials }` with
`Specials = Ieee | NanOnly | FiniteOnly` (`lib/std/num/float/float.hthr`).
Four gaps:

1. **Precision one** (`frac = 0`): [[float-precision-one]].
2. **Reserved top codes.** `Specials::reserves_top` is a `Bool`: the top
   binade loses its largest significand (E4M3's NaN). P3109 reserves 0, 1
   or 2 codes at the top of each sign's range (signed finite 0, signed
   extended 1, unsigned finite 1, unsigned extended 2). A count in place of
   the flag reproduces the paper's whole `emax` table *as a consequence*:
   at `P = 1` a binade has one significand, so a reserved code removes a
   binade (`emax` drops by one per code); at `P = 2`, two reserved codes
   remove the top binade; above that the binade only shrinks. Deriving
   `emax` from the reserved count instead of tabulating it is exactly what
   would have caught the report's errors. Open: whether `span` names the
   binades of the code space (and canonical form empties the reserved
   ones, which `max_finite` and `Format::max_mag_bounds` then have to
   survive) or the binades that hold finite values (so the constructor
   computes it).
3. **One zero.** `Finite` has `neg: Bool` and admits `-0`. A
   `signed_zero: Bool` in the format, with canonical form refusing
   `neg ∧ mag = 0` when it is false, keeps `Finite`'s shape; the operations'
   sign-of-zero theorems then split on it.
4. **Unsigned formats.** Canonical form refuses `neg` with a nonzero
   significand, and `Float::Inf(neg, has)` needs evidence that `neg` is
   allowed. What an operation does with a negative exact result in an
   unsigned format is the standard's to say (saturation to zero or NaN):
   read it before designing.

Whether `Specials` grows these cases or becomes a record (has infinities,
reserved count, signed zero, signedness) is the design round's choice; a
record is likely, since the cases are independent.

## Parts

- [[float-precision-one]]: `frac = 0` and the precision-one tie rule
  (`p3109-values`).
- [[float-saturation-modes]]: saturation as an operation parameter
  (`p3109-projection`).
- [[float-round-to-odd]], [[float-stochastic-rounding]]: the two new modes
  (`p3109-projection`).
- [[float-fast2sum-saturated]]: Fast2Sum's exact overflow error
  (`p3109-projection`).
- [[float-p3109-encoding]]: the bijection with `K`-bit patterns and the
  standard's tables (`p3109-encoding`).
- [[float-extract-scalar]]: Rump's splitting, whose fourth property fails at
  precision one (`math-float`).

## What it assumes from elsewhere

- **[[floating-point-formalization]]** owns `math-float` and
  `docs/library/floating-point-design.md`. Assumed here: only that a format
  is data indexing `Float(F)`, so a P3109 format is a new value, not a new
  type.

## Notes

Get the interim report (the paper's reference 20, the P3109 working
group's public repository) into `docs/papers/` before the design round;
the paper is a summary, and its tables are what the encoding gate checks
against.

## Log

- 2026-11-25: Design round done: `docs/library/float-p3109-design.md` (D1 datum = `Float(F)` up to `≈`, no `-0` change; D2 unsigned = nonnegative half of a signed envelope; D3 `cut` replaces `reserves_top`, `frac_ok` dropped; D4 ties to the even code; D5 the overflow tie follows the largest float's parity; D6 saturation is the projection round's). Round 1 (`p3109-values`) landed: `lib/std/num/float/p3109.hthr` builds `Binary{K,P,s,d}` from the reserved-code count, and the P3109 interim report v4.1 and its value tables (github.com/P3109/Public) are the reference; the tests check extremes against the tables. Remaining: [[float-saturation-modes]], [[float-round-to-odd]], [[float-stochastic-rounding]], [[float-p3109-encoding]].
- 2026-11-25: Round 2 (projection): saturation, unsigned projection, round to odd and stochastic rounding (pointwise, faithful), and Fast2Sum's overflow error landed; design §6.
