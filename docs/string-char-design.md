# `Char` and `String` as specification types — design

Status: **design, 2026-09-18**; owner `issues/string-char-spec-types.md`.
Settled in discussion the same day; this document records the decisions and
the first implementation round's scope. Heather code below is a sketch and
has not been checked.

## 1. Position

Under datarepr (`issues/datarepr-separation.md`) a spec type is mathematics
and a runtime representation is a certified refinement of it. So UTF-8 is
**not** the definition of `String`; it is the first repr of it, and the
encode/decode round-trip is the refinement theorem. What makes this
better-typed than Rust is exactly that split: Rust's `String` is bytes plus
an invariant, ours is a sequence of scalar values, and UTF-8 validity is a
theorem about the byte image rather than an invariant anyone can violate.

Three decisions:

1. **`Char` is a Unicode scalar value**, Rust-compatible: below `0x110000`
   and not a surrogate (`0xD800 ≤ c < 0xE000`). Surrogates are excluded so
   that UTF-8 encoding is injective and decoding is total on the image.
2. **`String` is a one-field record over `List<Char>`**, not an alias, so it
   owns its instance keys (literal class, `Decide` equality, a designated
   `++`) and the list lemmas lift through one projection.
3. **No `Utf8String`/`Utf32String` spec types.** "UTF-32" is the trivial
   repr of `String`, not a different string. Byte-level *meaning* (a hash, a
   wire protocol, a file offset) gets a separate spec type `Utf8` — a byte
   list with the validity witness — isomorphic to `String` through
   encode/decode; that type lands with the encode/decode round (§5), not now.
   Constant-time char indexing is a cost-basis requirement on the caller's
   repr choice (datarepr's `Impl` registry), never a type.

## 2. The types

Both records seal their witness behind propositional truncation, the
`BoundedList` pattern (`lib/std/bounded_list.hthr`): equality of values is
equality of the code (resp. the list) and rebuilding a witness cannot
disturb it. **Superseded for `Char` by §5.1**: a truncated witness cannot
refute a decoder, so `valid` is `IsTrue(is_scalar(code))` — relevant, unique,
and Bool-reflected. The sketch below is the round-1 shape; read §5.1 for the
witness and §5.5 for what landed.

```heather
// lib/std/char.hthr
fn scalar(code: Nat) → Type { code < 0x110000 ∧ ¬(0xD800 <= code ∧ code < 0xE000) }
fn scalar_dec(code: Nat) → scalar(code) ∨ ¬scalar(code)     // from the Nat deciders
instance(code: Nat) Decide<scalar(code)> { dec := scalar_dec(code) }

record Char {
    code: Nat,
    valid: ∥scalar(code)∥,
}
fn Char::toNat(self c: Char) → Nat { c.code }
fn ofNat(code: Nat, p: scalar(code)) → Char
fn Char::eq_dec ...                 // through `nat::eq_dec` on `code`
instance(a, b: Char) Decide<a = b> { dec := char_eq_dec(a, b) }
theorem code_injective(a, b: Char, p: a.code = b.code): a = b
```

`code_injective` is the lemma everything else rests on; it is the only place
the truncation is unpacked (squash is a `Prop`-level witness, so two records
with equal `code` are equal — the same argument `BoundedList` would make).

```heather
// lib/std/string.hthr
record String { chars: List<Char> }
designation ++ at String := append
fn String::len(self s: String) → Nat
fn String::nth(self s: String, i: Fin(s.len())) → Char
fn take(s: String, n: Nat) → String        fn drop(s: String, n: Nat) → String
theorem take_drop(s: String, n: Nat): take(s, n) ++ drop(s, n) = s
theorem len_append(s, t: String): (s ++ t).len() = s.len() + t.len()
theorem chars_injective(s, t: String, p: s.chars = t.chars): s = t
instance(s, t: String) Decide<s = t>
```

Everything is stated over `String` and proved by unfolding to the list
lemma once; do not re-prove list theorems. `nth` at `Fin(len)` is the
"better-typed" indexing: no partial index anywhere in the spec.

A `String` has exactly **one** presentation of its characters, and it is
`String` itself: no `List<Char>`-typed helper lives in `string.hthr`, and a
fact about lists is `list`'s (2026-09-18 review). Two consequences the
implementation had to find a spelling for:

- Equality decides through `list::list_eq_dec`, the generic decider whose
  premise is the carrier-level class `logic::DecEq<A>`. That class is the
  "future carrier-level equality class" `docs/decidable-equation-carrier-design.md`
  names: a `Decide<a = b>` instance is keyed by the endpoints' *resolved* type,
  so it says nothing at an abstract element type, which is exactly what a
  container's decider needs to require. `Nat`, `Char` and `List<A>` given
  `DecEq<A>` register it; `Decide<xs = ys>` at `List<A>` does not, for
  `issues/instance-binder-occurrence-through-binder-types.md`.
- `String::nth` is `s.chars.at(i)`: the total `Fin`-indexed read is a fact
  about every list, so it lives in `list.hthr` as `List::at`, and the string
  projects into it. A version recursing on the `String` itself was tried and
  rejected: the scrutinee is a projection, so it needs a `decreases` measure,
  which may not carry a `self` and leaves the recursion stuck at a neutral
  tail (`String(chars := Cons(c, rest)).nth(FS(k))` did not reduce to
  `String(chars := rest).nth(k)`). Through `List::at` every step reduces.

## 3. Literals

The lexer has no `'…'` or `"…"` tokens today. Two new token kinds and two
expression forms, mirroring carrier-directed numerals
(`docs/carrier-directed-numerals-design.md`): one syntax form each, never a
second literal for anything.

- **Lexing.** `'x'` is one scalar value (the lexer already reads UTF-8
  source, so the payload is Rust's `char` as a `u32`); `"…"` is a sequence
  of them. Escapes: `\n \t \r \\ \' \" \0` and `\u{hex}`; an escape
  producing a surrogate is a lexer error, so every lexed payload is a
  scalar by construction. Unterminated literals are lexer errors naming the
  opening quote.
- **Char literal.** In checking position at `Char` and in inference
  position it elaborates to `ofNat(n, p)` where `n` is the code's `Nat`
  literal and `p` is discharged by `Decide<scalar(n)>`: the elaborator
  builds the same term `decide<scalar(n)>()` would and takes the `Inl`
  branch, exactly as a `Fin` numeral discharges its bound today. A char
  literal never fails at the proof step because the lexer already refused
  surrogates. At any other expected carrier it resolves a class
  `CharLiteral<A> { ofChar: Char → A }` and applies `ofChar` (the `Numeral`
  route in `elab_overloaded_num_check`, `crates/elab/src/lib.rs`).
  *As landed:* the elaborator builds neither term itself. A char literal is
  the *surface* expression `char::ofNat(code, logic::decide_yes(refl))`
  re-elaborated, so the proof route is the one `decide` already owns
  (`crates/elab/src/literals.rs`).
- **String literal.** In inference position and at `String` it is
  `String(chars := <list literal of the char terms>)`, reusing the
  collection-literal lowering already owned by `List` — do not add a second
  list-building route. At another carrier it resolves
  `StringLiteral<A> { ofString: String → A }`. *As landed:* the classes
  live in `char.hthr` and `string.hthr`, not beside `Numeral` in `algebra`
  — each field names the type, so `algebra` would have had to import both
  modules and invert the library's dependency order. Placement rule: a
  literal class lives with the type its field names. Consequently the class
  is visible exactly when the type is: a literal at a carrier with no
  instance reports `no instance for CharLiteral<…>` (as `Numeral` does),
  and a literal in a program that has not imported the module reports
  that the type needs to be in scope.

Cost note, not a design input: a literal of *n* chars is *n* records over a
`NatLit` each, and vector literals once cost quadratically in the kernel
(`issues/elf-mutation-test-shape.md`, closed). Short literals are fine. When
a long literal bites, file it against `issues/packed-vector-literal-term.md`;
do not change the spec shape for it.

Two spellings the implementation settled (2026-09-18):

- `scalar_dec` decided its three bounds with `le_dec` directly, which
  descends both arguments together and is cheap at a closed code. The
  natural refutation through `lt_of_not_le` hit
  `issues/le-lt-conversion-linear-in-literal.md`: converting `k < Succ(n)`
  against `k <= n` at a literal `k` and neutral `n` costs a step per unit
  of `k`, so `nat`'s definitional `Lt ≡ Le ∘ Succ` is unusable at
  Unicode-sized constants. Filed, not worked around further. **Gone in §5.1**:
  the witness is a `Bool` now, so the decision is `bool::is_true_dec` at
  `is_scalar(code)` and no bound is compared twice.
- `take`, `drop`, `append` and `len_append` exist in both `list` and
  `string`; a file importing both qualifies (`string::take`). The receiver
  forms and `take_drop` are unambiguous.

## 4. Round 1 scope (this round)

1. `lib/std/char.hthr`, `lib/std/string.hthr` as in §2, in stdlib style
   (`docs/stdlib-style.md`); exports from `lib/std` follow the existing
   modules' import discipline.
2. Lexer, AST and parser forms for both literals, with lexer unit tests
   (escapes, surrogate refusal, unterminated).
3. Elaboration of both literals as in §3, including the two classes, with
   tests in `crates/elab/tests/` shaped like `carrier_numerals.rs`: a char
   literal at `Char`, a string literal at `String`, each at a user carrier
   through the class, a literal at a wrong type reporting a mismatch, and
   an inference-position literal.
4. A small showcase check under `crates/cli/tests/fixtures` or the semantic
   suite exercising `nth`, `take_drop`, `len_append` and `Decide<s = t>` on
   literals, following `docs/testing-generated-terms.md` for the theorem
   sites (a literal *and* a neutral string, and a negative control).

Out of scope for round 1: UTF-8 encode/decode and the `Utf8` type (§5), any
repr, char classes (`is_digit` and friends), a `Char`-token lexer for the
parser library (its natural first consumer, `docs/parser-library.md`, which
today has no string lexer by design), case mapping, graphemes.

## 5. Round 2: UTF-8 encode/decode and the `Utf8` type

Charter 2026-09-18, after round 1 landed. Pure mathematics on the spec side;
nothing here waits on `issues/byte-memory-access-model.md`. `encode` is also
the `abs` the future byte repr will use.

### 5.1 Finding: a truncated witness cannot refute a decoder

The round-trip theorem `decode(encode(c)) = Some(c)` has to show that the
decoder's rejection branch is unreachable at a scalar value, i.e. derive
`False` from `c.valid` and the branch's `¬scalar(c.code)`. With
`valid: ∥scalar(code)∥` that is impossible: the squash eliminator lands only
in squash-headed types (`crates/kernel/src/typing.rs`, `ElimSquash`;
`issues/sprop-squash.md`), so the best one gets is `∥False∥`, and the
theorem could only be stated as `∥decode(encode(c)) = Some(c)∥`. Every
consumer that decodes hits the same wall. Truncation was the wrong seal for
a witness that computation has to *use*; it was right for `BoundedList`
only because nothing unpacks `fit`.

**Decision: `Char`'s witness becomes Bool-reflected and relevant.**

```heather
fn is_scalar(code: Nat) → Bool {
    leb(Succ(code), 0x110000) && not(leb(0xD800, code) && leb(Succ(code), 0xE000))
}
fn scalar(code: Nat) → Type { IsTrue(is_scalar(code)) }   // IsTrue(True) = True, IsTrue(False) = False
record Char { code: Nat, valid: scalar(code) }
```

Proofs of `scalar(code)` are unique: case on `is_scalar(code)` with the
match equation; in the `True` case both witnesses inhabit `Unit`, which has
definitional η (`crates/kernel/DESIGN.md`), so `refl`; the `False` case is
absurd. `code_injective` follows exactly as before, now through that lemma
instead of squash irrelevance. `Decide<scalar(code)>` is the match on
`is_scalar(code)` — `scalar_dec`'s three `le_dec`s go away, which is the
shape `issues/derive-decide-instances.md` wants anyway. `ofNat(code, p)` keeps
its signature, so `crates/elab/src/literals.rs` and the literal route are
untouched. `scalar_sound: scalar(code) → code < 0x110000 ∧ ¬(…)` is stated
once for clients that want the arithmetic reading (`nat`'s `leb`/`Le`
bridge lemmas; find them before proving new ones).

`Utf8`'s validity witness (§5.4) is Bool-reflected for the same reason.

### 5.2 Encoding: bits, not division

`nat::div`/`mod` are unary in the dividend (`divmod` recurses on `n`), so a
digit split of `0x10FFFF` would cost a million steps. UTF-8 is bit
shuffling, and `bitvec` already has the pieces with their laws:
`concat(n, m, lo, hi) : BitVec(m + n)` (low bits first), `split(n, m, x)`,
`split_concat_low`/`split_concat_high`/`concat_split`, and `ofNat(n, x)`
bounded by the width. Bit index 0 is the least significant bit, so a
continuation byte `10xxxxxx` is `concat(6, 2, payload, from_bits(2, [False, True]))`.

```heather
// lib/std/utf8.hthr   (imports: logic, nat, bool, list, option, pair, bitvec, char, string)
fn encode_char(c: Char) → List<BitVec(8)>     // 1–4 bytes, branch on leb(…) against 0x80, 0x800, 0x10000
fn encode(s: String) → List<BitVec(8)>        // concat_map of encode_char over s.chars
```

Per range the payload is `ofNat(w, code)` at the exact width `w` (7, 11,
16, 21) and the bytes are `split`s of it under fixed headers (`110`,
`1110`, `11110`, `10`), spelled with `from_bits` literals. The branch
decisions are `leb` with match equations, so the proofs can rewrite along
them.

### 5.3 Decoding, strict

```heather
fn decode_char(bytes: List<BitVec(8)>) → Option<Pair<Char, List<BitVec(8)>>>
fn decode(bytes: List<BitVec(8)>) → Option<String>
```

`decode_char` classifies the lead byte by `split(…)` against the headers,
takes exactly the continuation bytes the header promises (each checked for
`10`), reassembles the payload with `concat` at the width, and takes
`toNat`. It then **rejects** overlong forms (a 2-byte value below `0x80`,
3-byte below `0x800`, 4-byte below `0x10000`), non-scalars (surrogates,
above `0x10FFFF`, both via `is_scalar`), lead bytes `0xC0`/`0xC1`/`0xF5`+
(they fall out of the same checks), and truncation. Rust's `from_utf8`
semantics exactly. `decode` iterates `decode_char` structurally on the
byte list: each step consumes a non-empty prefix, and the recursion is on
the remaining tail, which is a sub-term.

### 5.4 The `Utf8` type and the theorems

```heather
fn is_utf8(bytes: List<BitVec(8)>) → Bool          // decode(bytes) is Some
fn utf8_valid(bytes: List<BitVec(8)>) → Type { IsTrue(is_utf8(bytes)) }
record Utf8 { bytes: List<BitVec(8)>, valid: utf8_valid(bytes) }
fn Utf8::len(self u: Utf8) → Nat                    // byte length; String::len counts chars
fn ofString(s: String) → Utf8                       // encode, witness from round-trip
fn Utf8::toString(self u: Utf8) → String            // decode, the witness refutes None
```

Theorems, in the order to prove them:

1. `toNat_ofNat(n: Nat, x: Nat, x < 2^n): toNat(n, ofNat(n, x)) = x` —
   **verification item**: `bitvec.hthr` may not have it (no theorem names
   `ofNat`); find it or prove it from `half`/`odd_bit` (`nat.hthr` has
   `half_double`, `half_add_half`). Do this first; it gates everything.
2. `decode_char_encode_char(c: Char, rest): decode_char(encode_char(c) ++ rest) = Some(Pair(c, rest))`
   — four cases along the encoder's `leb` equations; `split_concat_*` undo
   the byte assembly, `concat_split` the payload, `toNat_ofNat` the value,
   and the decoder's rejection checks are the same `leb`/`is_scalar` terms
   as the encoder's branch and `c.valid`, so they rewrite closed.
3. `decode_encode(s: String): decode(encode(s)) = Some(s)` — induction on
   `s.chars` through 2 and `chars_injective`.
4. `encode_injective(s, t: String, p: encode(s) = encode(t)): s = t` — from 3.
5. `encode_append(s, t: String): encode(s ++ t) = encode(s) ++ encode(t)`.
6. `toString_ofString(s): ofString(s).toString() = s` — from 3.
7. `encode_decode(bytes, s, p: decode(bytes) = Some(s)): encode(s) = bytes`
   — the strictness theorem, which is what makes `Utf8 ≅ String`; with it
   `ofString_toString(u): ofString(u.toString()) = u` through a
   `bytes_injective` for `Utf8`. This is the hardest item: per byte class,
   a decoded value re-encodes to the same bytes because the overlong checks
   pin the width. **If it does not close in the round, land 1–6 and report
   exactly where 7 stalls; do not weaken the decoder to make it easier.**

Out of scope: `Utf8 ++`, byte-level slicing, char classes, the parser
library's lexer, any runtime repr.

### 5.5 As landed (2026-09-18)

Theorems 1–6 closed; 7 did not, and the stop rule was taken. What the
implementation had to settle, and what a later round should read first:

- **`IsTrue` and its kit live in `bool`, not in `char`.** `IsTrue`,
  `is_true_unique`, `is_true_dec` with its `Decide` instance, the four
  connective bridges, and the two rewrites a consumer needs
  (`eq_true_of_is_true`, `is_true_dec_yes`) are facts about a reflected
  Boolean; `char::scalar` is one client and `utf8::utf8_valid` the second.
  `nat` gained the `leb`/`Le` bridge (`leb_sound`, `leb_complete`,
  `le_of_not_lt`, `leb_not_lt`) — **there was none**, as §5.1 suspected.
- **Theorem 1 was not in `bitvec`.** `toNat_ofNat` is now there, proved on
  the WIDTH from the digit equation `odd_bit_add_twice_half` and a new
  `nat::half_lt_of_lt_double` (the bound halves as the argument loses a bit).
- **Vectors have definitional η.** `take_low(3, 5, concat(3, 5, lo, hi)) = lo`
  is `refl` at an open `lo`, so at the literal widths UTF-8 uses, every
  byte-level split/join round trip is computation and `split_concat_low`,
  `split_concat_high` and `concat_split` are never cited. The encoder's
  nested `take_low`/`drop_low` and the decoder's nested `concat` were
  written to mirror each other so that this is so.
- **`decode` recurses on a fuel, and the fuel is the byte count.** A
  structural recursion on the byte list is impossible — only an *immediate*
  tail may carry a self-call, and a three-byte class consumes a grandchild —
  and `decreases list_len(bytes)` is worse than impossible: the measure
  proofs need the `match`'s equation bindings, and a `decreases` body written
  with those gets **no unfolding equation**
  (`docs/decreases-unfolding-design.md` §3), so nothing about it is provable
  at an open tail. `Nat` admits course-of-values recursion, so a fuel spent
  exactly as many steps as bytes consumed does not, and the recursive call
  in the proof is the induction hypothesis with no fuel arithmetic between.
- **A conversion pathology shaped one statement, until it was fixed.**
  Converting `decode` at a three- or four-byte sequence against a term that
  also names `decode_char`/`decode_seq` died in the kernel, while converting
  it against the same term one delta-step further reduced (`emit`) was
  cheap, so the list step was first stated at `emit`. The cause was the
  kernel's reaction to a failed same-head meet — the two sides share `bit7`
  as the δ-head of *different* matches, and normalizing both from there
  unrolled `nat::leb(0x800, code)` at a stuck `code` past the depth budget
  (`issues/utf8-decode-conversion-blowup.md`, closed 2026-09-18). The step
  is now `decode_step`, the natural statement: decoding a list is decoding
  its head and then its tail, by computation at every width.
- **Theorem 7 stalls on inversion, not on arithmetic.** Its hypothesis is
  `decode(bytes) = Some(s)` at an *abstract* byte list, so the proof has to
  case on `class_of(b)` — and the class is not an argument of `decode_at`,
  it is computed inside its body, so there is no motive to abstract it with.
  Naming the per-class body (as `decode_seq` names `decode_char`'s) does not
  work here because that body makes the recursive call, so the pair would be
  mutually recursive, and `docs/mutual-recursion-design.md` requires
  `decreases` on every member of such a group — back to the unfolding
  problem above. The way through is to hoist the four tail results out of
  the class dispatch so the per-class body takes them as `Option<String>`
  arguments and stops being recursive; then the remaining work is ordinary:
  `bitvec::ofNat_toNat` and `bitvec::toNat_lt_pow` (neither exists), the five
  "rebuild the byte from its payload and its class bits" lemmas, the
  converse of `width_bounds` (a class's range tests determine `width_of`),
  and inversion lemmas for `push_char` and `emit`.

