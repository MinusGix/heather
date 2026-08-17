# Telling `D<A, B>` from `a < b`

How Heather decides whether a `<` opens a type-argument list or is the
comparison operator. Landed 2026-08-16; the tracking issues are
`issues/comparison-inside-type-arguments.md` (closed by this) and
`issues/type-argument-speculation-cost.md`.

The rule, in one sentence:

> **A `<` with whitespace before it never opens a type-argument list. A tight
> `<` is *speculated* as opening one, and falls back to comparison if that
> parse does not complete.**

## 1. Why this is hard here and not in Rust

Rust has the same two readings of `<` and resolves them by keeping types a
separate syntactic category: no type contains `<` the operator, so the
ambiguity lives only on the expression side and the turbofish settles it.

Heather cannot borrow that, and the reason is not incidental. **Propositions
are types.** Since 2026-08-16 `n < m` *is* `Lt(n, m)`, a type, written exactly
where a hypothesis goes — `h: i < len(xs)` (`docs/nat-order-design.md`). So
`<`-the-bracket and `<`-the-operator occur in the same positions, in both
grammars, and no separation of categories is available to appeal to.

## 2. Speculation, and the thing it provably cannot do

The first answer was speculative parsing at both sites — `Parser::try_tyargs`
in the expression grammar and the `D<A, B>` branch of `Parser::ty`: try the
type arguments, and if the parse does not complete, rewind and take the
operator reading. Total, so unlike a lookahead heuristic it cannot be wrong
about a program.

It has a hole, and the hole is not an implementation gap:

```heather
Or<n < m, m <= n>        -- was a parse error
```

The inner `n <` speculates too, and **succeeds** — it reads `m, m <= n` as its
own type arguments and consumes the `>` that was supposed to close the outer
list. The outer parse then finds no bracket, rewinds, and reports something
about `Or`.

The tempting repair — turn inner speculation off inside a type-argument list —
breaks `List<Option<Nat>>`, which *needs* it. So the choice is **per
argument**:

```heather
Or<Option<Nat>, n < m>   -- argument 1 needs speculation ON
Or<n < m, Option<Nat>>   -- argument 1 needs it OFF
```

and trying the combinations is exponential in the argument count. **Complete
disambiguation by backtracking alone would require GLR/Earley-style parsing.**
Every language that keeps `<…>` ends up requiring a marker in this position
for the same reason; it is a property of the notation, not of the parser.

## 3. What the whitespace rule adds, and what it deliberately does not

The rule supplies the one bit backtracking cannot recover: which `<`s are
*eligible* to be brackets. In `Or<n < m, m <= n>` the inner ` < ` is spaced, so
it cannot open a list, so it cannot steal the `>`, and the outer parse
completes. No parentheses, no new syntax.

**It is one-directional, and that word carries the safety argument.** Spacing
can only *narrow* the ambiguity:

| spelling | reading |
| --- | --- |
| `a < b` (spaced) | comparison, decided — no speculation runs |
| `a<b` (tight) | *speculated*; no closing `>`, so it falls back to comparison |
| `List<Nat>` (tight) | speculated; completes, so type arguments |
| `List <Nat>` (spaced) | comparison, then a stray `>` — an error (§5) |

A tight `<` is **not** thereby a bracket. That is what keeps the rule from
being "formatting is semantic": every program that parsed before the rule
still parses, `a<b` as a comparison included, and the only spelling that
changes meaning is `List <Nat>` — which occurred **zero times** in `lib/` and
the test corpus when the rule landed, alongside zero tight comparisons.

Newlines count as whitespace, deliberately. Keeping the rule to one sentence is
worth more than `List\n<Nat>`, and wrapping a long type argument list works by
breaking *inside* the brackets, where the `<` is still tight:

```heather
List<
    Option<Nat>
>
```

## 4. Where the ambiguity still is

Only at **use** sites, and only at tight `<`. Declaration sites were never
ambiguous and never speculated: after `fn name`, in a constraint head
`<A: Monoid(op)>`, or after `instance`, a `<` can only open type parameters.
That is worth stating because it is where most of the notation's readability
lives, and none of it was ever at risk.

Speculation therefore remains, for tight `<` only, with the failure memo of
`issues/type-argument-speculation-cost.md` keeping it linear.

## 5. The diagnostic

`>` is not an operator anywhere in Heather (`lexer.rs:40`); it only ever closes
a type-argument list. So a stray `>` has exactly one cause — its `<` was read
as a comparison — and `Parser::expect` says so directly rather than reporting
whatever token it wanted. No scanning and no guessing which `<` is at fault:

```
expected `)`, found `>` — `>` is not an operator and only ever closes a
type-argument list, so its `<` was read as a comparison. A `<` with a space
before it always is one: write `List<Nat>`, not `List <Nat>`
```

## 6. The commitment this makes

`>` must stay a non-operator: it is the closing bracket, and the diagnostic
above and the speculation in §2 both lean on there being no other reading. So
`>` and `>=` cannot become plain infix operators.

They are already held back on the argument-flip caution
(`issues/nat-order-kit.md`), so nothing is lost today, and the escape if they
are ever wanted is Unicode — `≥` is a distinct token and stays free. Worth
recording as a real commitment rather than a coincidence, because it is now
load-bearing in three places.

## 7. Rejected alternatives

- **A brace marker**, `Or<{n < m}, {m <= n}>`. Works — a marker is the other
  half of §2's theorem — but **parentheses already are that marker**, already
  parse, and are already this language's stated escape hatch (`Parser::no_eq`
  and `Parser::no_record_lit` both document "lifted inside any bracket, so the
  escape hatch is a parenthesis"). A second mechanism for one job. Parens
  remain available and remain correct; the rule just stops them being
  mandatory.
- **The hard whitespace rule** — tight `<` *is* a bracket. Complete, and it
  would even un-block `>`/`>=`, but it makes `a<b` a misparse forever for
  anyone with C habits, and it decides a meaning rather than narrowing an
  ambiguity. The one-directional form gets the residue fixed without that.
- **A name table** — `<` opens type arguments iff the head is a declared
  parameterized name. Makes parsing depend on imports and on a pre-pass, and
  breaks under shadowing.
- **Capitalization** — dead on the corpus: `or_pick<P, Q, A>`,
  `false_elim<P>`, `iff_trans<P, Q, R>` are all lowercase generic
  declarations.
- **Retiring `<…>` for plain application**, `Or(Nat, Nat)`. Recorded and
  declined in `issues/retire-angle-bracket-type-arguments.md`: the notation
  earns its keep by demoting type arguments out of the value-argument stream,
  which is exactly what a reader wants of them, and the constraint heads read
  well. The *additional* spelling `Or(Nat, Nat)` is still wanted and is
  tracked there.
