# A scannerless `String` calculator, over an abstract parser source — design

Status: **design, 2026-09-18**; owner `issues/sequence-parser-source.md`. Every
shape below was hand-run on the tree at 3d10b94 with a freshly built release
binary before it was written; the probes are `probes/str/p3@ef3961a`–`p13`.

## 1. Position

`String` landed as a specification type with no consumer
(`issues/string-char-spec-types.md` closes on "later, behind a consumer: a
`Char`-token lexer for the parser library"), and the parser library's
`docs/library/parser-library.md` declares "no string lexer" a non-goal. Both are
answered by the same artifact: a calculator whose source *is* the text.

Two decisions, taken in discussion 2026-09-18.

**The calculator is scannerless**, not a lexer feeding the token grammar. The
reason is a proof obligation, not taste: a `TNum(n)` token has thrown its
digits away, so relating a token-level derivation back to the characters needs
a `Nat`-to-decimal rendering function and a render/parse round-trip theorem. A
`Number` production that carries its *digits* needs neither — `spelling` is
those characters and `meaning` is the decimal fold — so the scannerless grammar
is both the smaller artifact and the stronger statement.

**Whitespace is carried in the derivation.** Each lexeme owns its trailing
spaces and the whole parse owns its leading ones, with `WellFormed` obliging
every such character to be a space. The alternative — a skip pass before the
grammar — would leave the span theorem talking about stripped text rather than
about the input, which is precisely the guarantee the showcase exists to make.

## 2. What the probes settled about the source abstraction

The parser library's source is `List<T>` throughout. Making it abstract is
`issues/sequence-parser-source.md` rounds 4–5; these are the constraints any
such design has to satisfy, each measured rather than assumed.

1. **Nothing is needed for `String` to work today.** `Cursor<T>(source: List<T>)`
   accepts `s.chars`, and `run_string(p, s) = run(p, s.chars)` is a one-liner.
   `run_string(some(digit), "123") = Ok([1,2,3])` holds by `refl` (`p2`).
2. **A rank-2 `run` field is not expressible.** A record field cannot quantify
   over a constrained type parameter, so a token-indexed `Parser<T, A>` whose
   `run` is polymorphic in the source is out (`p5`). Genericity must live in
   the function signatures — which is where the library already keeps it.
3. **The class needs two parameters, not an associated element type.** With
   `class Seq<S> { Elem: Type, … }` a grammar cannot say "my element type is
   `PTok`"; `<S: Sequence<PTok>>` says exactly that, and resolution has no
   hole because the source argument determines `S` (`p4`, `p6`). A
   one-parameter class also fails inference wherever no argument mentions the
   element type.
4. **The operations travel as an index parameter.** A record's type parameters
   cannot carry a constraint, so the shape is `finite_set`'s: a `SeqOps<S, T>`
   operations record, a `Sequence<S, T>(ops)` class holding the laws, and
   `Cursor<S, T>(ops, source)` indexed by the operations. An instance index
   must be a bare global reference (`string_ops`, not `string_ops()`).
5. **The whole shape checks and computes** (`p7`): `Cursor<S, T>(ops, source)`
   with `within: Le(offset, ops.seq_len(source))`, a token-fixed
   source-polymorphic consumer, and `refl` equations at **both** `String` and
   `List<Char>` — so a grammar written once runs on either.

The laws a source owes are `len_view`, `drop_view` and an uncons agreeing with
the view; every existing parser law is then its list counterpart through
`ops.view`, and both instances discharge the laws by `refl`. The cost is the
churn: 1082 lines over seven modules, 128 signature sites mentioning the
source, eight records gaining an index.

## 3. The character kit

`lib/std/text/char.hthr` gains `is_digit`, `is_space` and `code_is` as `Bool`
programs over the code — `is_scalar`'s spelling, so a closed character decides
by descending two literals together — plus `digit_val`, the `Option` form
`digit_of` that `parser::recognize` takes, and four facts: `digit_selected`
inverts `digit_of`, `digit_val_lt` bounds a digit by ten, and
`code_is_sound`/`code_is_char` turn a passed code test back into an equality of
characters. `selected_of_match` is the inversion stated at an abstract `Bool`
and applied at the computed class, because a `match` on the class alone does
not refine `digit_of(c)`.

`lib/std/data/list.hthr` gains `cong_append_r`, the missing counterpart of
`cong_append_l` (clients threading a span through a fixed prefix wrote that `j`
by hand), and `List::nonempty` / `List::all` beside its existing `is_nil` — the
elementwise class test takes a `Bool` program because that is what a decidable
class is, and reflects it with `IsTrue` one element at a time, so a witness is a
nested pair a caller builds positionally.

## 3.1 What a readability pass found in the language

The showcase was then read as a language-quality target, and four of the five
complaints were answered by features that already work; the fifth and two
further findings are filed.

- `A ∧ B` works wherever the showcase wrote `And<A, B>`, and receiver members
  work on a user-declared inductive: `Derivation::tier` called as `d.tier()`,
  including **inside a record field's type** (`valid: derivation.WellFormed()`).
  So the derivation's whole theory is namespaced, and `all_of`/`nonempty` are
  `list`'s generics reached as `ds.all(is_digit)` and `ds.nonempty()`.
- A record type **cannot be partially applied**, which is the only reason
  `GrammarSpec` exists beside `Grammar` — `issues/record-type-partial-application.md`.
- A type-owned member is reachable *only* through a receiver; the qualified form
  `Type::member(args)` is refused. Logged on `issues/type-owned-namespaces.md`, whose
  non-receiver half this is.
- Because of that, an analysis that does not understand receivers is a hard
  block rather than a style tax: IH generalization does not see a self-call
  spelled as a receiver, so a structurally recursive member that varies a
  non-decreasing parameter has **no spelling that checks**
  (`issues/receiver-member-ih-generalization.md`). `spell` is therefore the one
  declaration in the file that stays freestanding, and it is exactly the
  difference-list idiom §5 credits with removing every `append_assoc`.
- Seven declarations are `fn … → Type` and read like programs that happen to
  return types; a `type` declaration form is `issues/type-declaration-form.md`.

## 4. The certified run, and the library gap it names

A multi-digit numeral is the first thing in the tree that **repeats and has to
prove what it consumed**. `many`/`some` carry a `Consumes` certificate but no
`Post` contract, so there is nothing to compose — `issues/parser-certified-repetition.md`.
The showcase therefore hand-rolls `checked_run`, a certified run of characters
in a class:

```heather
fn RunSpec(cls, source, begin, end, cs) → Type {
    cs.all(cls) ∧ (rest(source, begin) = cs ++ rest(source, end))
}
```

It is *total* — an empty run is a run — so it returns a `Certified` rather than
a `Reply`, and it is the general contract at one relation in about twenty
lines. Digits and spaces are both instances of it. This is the datum for what
`many_post` should say, not a workaround to keep.

## 5. The spelling is a difference list

`spell(d, tail)` rather than `spelling(d) ++ tail`. Consequence: **no
`append_assoc` appears in the showcase at all**, where the token version needs
a three-way `span_join` at every production. Each production's span proof is
`trans(l.span, l.derivation.cong_spell(…))` — a congruence under
`spell(d, ·)` applied to the next cursor's equation. `spelling(d)` is
`spell(d, Nil)`, so the whole-input theorem also drops `append_nil`.

## 6. Cost, and why the showcase is not yet in the suite

`docs/showcase/calc_text.hthr` checks green through the CLI and every one of
its fifteen `refl` equations holds, including `calculate(" 2 + 3 * 4 ") = Ok(14)`
and five error cases. It needs **more than 8 GiB** cold: it passes at 20 GiB
and dies at the 6 GiB per-process rail `scripts/test` sets, so it is *not*
wired into `crates/elab/tests/showcase_calculator.rs` beside `calc_parser`.

The cause is measured and is not the grammar's shape. A record token type costs
**27× the conversion misses** of an inductive one in a controlled pair
(`probes/str/p10.hthr@ef3961a`, 1,527,745 against 56,662 with every other line
identical), which is `issues/elaborator-canonical-type-spelling.md`'s group-B
disagreement reached from the type-argument end: `Cursor<Char>`, `List<Char>`
and `Certified<Char, List<Char>>` each instantiate the library at a record.
`calc_parser`'s structurally identical tier bodies cost 188–204 misses where
these cost 290–450 k.

Two spellings were tried and neither is the lever: the `Result` eliminators
instead of nested `match` cut misses 2.9× (854 k → 291 k, and are the better
style regardless — `calc_parser` says so in its own comment), and returning the
library's `Certified` instead of a purpose-built indexed record left them flat.
Threading a placeholder `Nat` rather than the character through
`Recognized`/`Certified` is worth 21% on the one item that does it. Wiring the
showcase into the suite waits on the defect, not on another spelling.
