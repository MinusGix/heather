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
disturb it.

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

- `scalar_dec` decides its three bounds with `le_dec` directly, which
  descends both arguments together and is cheap at a closed code. The
  natural refutation through `lt_of_not_le` hit
  `issues/le-lt-conversion-linear-in-literal.md`: converting `k < Succ(n)`
  against `k <= n` at a literal `k` and neutral `n` costs a step per unit
  of `k`, so `nat`'s definitional `Lt ≡ Le ∘ Succ` is unusable at
  Unicode-sized constants. Filed, not worked around further.
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

## 5. Round 2 sketch (not this round)

`encode : String → List<BitVec(8)>`, `decode : List<BitVec(8)> → Option<String>`,
`decode(encode(s)) = Some(s)`, the byte-list validity predicate
`utf8_valid`, and `record Utf8 { bytes: List<BitVec(8)>, valid: ∥utf8_valid(bytes)∥ }`
with the iso to `String`. Pure mathematics on the spec side; it is also the
`abs` the future byte repr will use, so nothing here waits on
`issues/byte-memory-access-model.md`.
