# Fixed-width integers: `u8`, `i8`, and any `u27`

Status: **landed** (first slice). Issue: `issues/byte-type-and-predicates.md`,
widened by Minus on 2026-11-02 from "a name for `BitVec(8)`" to "write any
`u27`, and signed `i8` and such, which may behave differently from `BitVec`".

## 1. What a program writes

```heather
fn checksum(xs: List<u8>) → u8 { … }          // u8 is BitVec(8)
fn mean(a, b: i64) → i64 { (a + b).div(2) }   // i64 is SInt(64): signed div
fn field(x: u27) → u32 { x.zero_extend(5) }   // any width
fn at(n: Nat, a: i(n)) → i(n) { -a }          // an open width
```

`u8`/`u16`/`u27`/`u64` are words read unsigned and *are* `BitVec(n)`.
`i8`/`i27`/`i64` are words read in two's complement, a type of their own,
`SInt(n)` (`lib/std/bitvec/sint.hthr`).

## 2. Names for types: a `def` at a universe

`docs/types-as-expressions.md` chose, by explicit decision, a type-valued
`fn` over a `type` declaration: a `fn F(…) → Type` is the abbreviation
mechanism, and a `type` keyword would be a second one. This round keeps
that and closes the two gaps that made `def u8: Type = BitVec(8);` refuse:

1. **A bare `def` at a universe names its type.** `u8` in type position,
   where `u8` is a global `def` of type `Type<l>`, lowers to the type it
   denotes (`inductive.rs`, `lower_type_value`). A `def` of any other type
   is refused naming its type.
2. **It is expanded on the spot.** A type-valued `fn` call is `El` of the
   call and unfolds lazily, in conversion, which is the right cost model for
   `Refines(p, i, q, j)`. It is the wrong one for a name: every head-keyed
   table — `Numeral`/`CharLiteral` instances, instance search, designations,
   the native frontend's readers — would see `El(u8)` where it keys on
   `BitVec`. Probed before this round: at `fn UInt(n) → Type { BitVec(n) }`,
   methods and `<` worked, and a numeral at a declared `UInt(8)` result did
   not. So a `def` is δ-unfolded and decoded (`decode_deep`) when it is
   read in type position, and nothing after that point can tell `u8` from
   `BitVec(8)`. A `def` has nothing to compute, which is what makes eager
   expansion safe where it would not be for a `fn` that matches on its
   argument.

### 2.1 The cost of eager expansion

Diagnostics print `BitVec(8)` where the program wrote `u8`. That is the
same trade `let`-bound type aliases already make, and it is the honest
spelling of the type. Respelling by the name written is display work
(`issues/type-name-display-respelling.md`).

### 2.2 Width families: `u27`

`def u: Nat → Type = BitVec;` is a **width family**. A type name that does
not resolve and splits as a family name ending in a letter plus a decimal
width with no leading zero — `u27`, `i64`, not `u08`, not `x_1` — means the
family applied, `u(27)`, if the family part is a global `def`
(`split_width`). The applied spelling `u(n)` / `i(n)` at an open width is
expanded the same way (`try_type_value_app`), so generic code reads as the
closed code does.

A local binder does not hide a family: `fn f(i: Nat, x: i64)` works, because
`i64` is read in type position where no local value could have been meant,
and `i`/`u` are the commonest binder names there are. (Shadowed, the family is
elaborated by its module-qualified name, which no local can be.) A global
`def` named `u27` itself still wins over the family reading.

Nothing in the rule is specific to integers: any `def F: Nat → Type<l>`
gets `F8`. The library declares exactly two, `u` (`bitvec.hthr`) and `i`
(`sint.hthr`).

## 3. Why `i8` is its own type and `u8` is not

The operators that differ between the two readings of a word:

| operation | `u8` (`BitVec(8)`) | `i8` (`SInt(8)`) |
|---|---|---|
| `<`, `<=` | unsigned (`unsigned_lt`) | signed (`signed_lt`) |
| division, remainder | `udiv`/`urem` | `div`/`rem`, truncating toward zero |
| right shift | `shift_right`, zero-fill | `shift_right` copies the sign; `logical_shift_right` |
| widening | `zero_extend` | `extend`, sign-extending |
| numeral `-1` | `255` | `-1` (all ones) |
| value | `toNat` | `toInt` |
| overflow | carry (`carry_add`) | `overflows_add`/`overflows_sub` |

and the ones that do not: `+`, `-`, `*`, `neg`, the bitwise operations,
`shift_left`, equality, truncation.

A designation is keyed by the carrier's head (`docs/operators-onto-classes-
design.md` §3), and so are numerals and instances. Two readings with
different `<` therefore need two heads. `u8` takes `BitVec`'s, because
`BitVec` already reads unsigned — its `<` is `unsigned_lt`, its numerals are
`ofNat` — and is the type the whole native library is written over: a `u8`
that were a wrapper would make every native lowering see through it, for no
behaviour that differs. `i8` takes a new head, `record SInt(n: Nat) { bits:
BitVec(n) }`: every operation the readings share is the word's applied to
`bits`, so the `BitVec` laws reach it through the field (`SInt::add_comm`
is one `cong`), and the ones that differ are its own.

The option not taken is a signless `BitVec` with both `UInt(n)` and
`SInt(n)` wrappers (Lean's `UInt8`/`Int8` over `BitVec 8`). It is the more
symmetric design and buys one thing: `BitVec` with no order at all. It
costs a wrapper on the most common type in the native library, and was
declined (Minus, 2026-11-03).

## 4. Division

There was none. `lib/std/bitvec/bitvec_div.hthr` adds it as **restoring long
division** over the dividend's bits, most significant first, with the
remainder one bit wider than the divisor so a step's double-and-add cannot
carry out. A closed quotient costs the width squared and never the operands'
magnitude, which is the module's standing rule
(`docs/bitvec-width-bounded-defaults-design.md`): a `u64` divides by
evaluation in 64 steps, where `Nat::div` through `toNat` counts down one
successor at a time and could not finish.

By zero, it is SMT-LIB's convention, and it is what the long division computes
with no special case: `x / 0` is all ones and `x % 0` is `x`. Signed division
is SMT-LIB's `bvsdiv`/`bvsrem` read off the magnitudes: truncation toward zero
(C, Rust, x86 `IDIV`, LLVM `sdiv`), the remainder takes the dividend's sign,
`MIN / -1` wraps to `MIN`, and nothing traps. Lean's `BitVec` chose `x / 0 =
0` instead; either is a total convention, and SMT-LIB's is the one a solver
and a bit-blasted certificate already agree on.

## 5. Byte classes

`lib/std/bitvec/byte.hthr` gains the C locale's `<ctype.h>` classes as
methods on `u8`: `is_space` (`isspace`, with vertical tab and form feed, which
`Char::is_space` leaves out), `is_newline`, `is_blank`, `is_digit`,
`is_upper`/`is_lower`/`is_alpha`/`is_alnum`, `is_xdigit`, `is_print`,
`is_control`, `is_ascii`. Each is `eq_bit`/`unsigned_lt_bit` comparisons
joined by `&&`/`||`, which is what the structured frontend splits a byte test
at.

## 6. Open

- ~~The decision for Minus~~ Decided (Minus, 2026-11-03): `u8` stays
  `BitVec(8)`; only signed words are a record (§3).
- **Operator symbols.** `/`, `%`, `<<`, `>>`, `&`, `|` do not lex today;
  division and shifts are methods. `issues/integer-operator-symbols.md`.
- **Division laws.** The Euclidean characterization of `udivrem` (`a = q·d +
  r`, `r < d` for `d ≠ 0`) is unproved; the probes are closed values.
  `issues/bitvec-division-laws.md`.
- **Native lowering of `SInt`.** The native frontend reads `BitVec` words;
  an `SInt` field is one record level above them.
  `issues/sint-native-lowering.md`.
- **Display.** `issues/type-name-display-respelling.md` (§2.1).
