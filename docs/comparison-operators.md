# The comparison level: `<=`, `<`, and `=` on one non-associative rung

Tracking issue: `issues/comparison-operators.md`. Prerequisite:
`issues/le-named-proposition.md` (the desugar target has to exist before the
notation can name it). Background: `issues/surface-operators.md`, whose
`infix_op` table this round deliberately does **not** grow.

---

## 1. What the round adds

One lexer token and one parser rung.

```heather
theorem fuel_monotone(…, h: eval(n, prog)(env, ir) = Out(vs), hle: n <= m)
    : eval(m, prog)(env, ir) = Out(vs)
```

`n <= m` is `Le(n, m)` — the **proposition** from `lib/ir_v1.hthr`, a `fn`
returning `Type` whose body is the reflection equation `leb(n)(m) = True`. It
is not the boolean and it is not context-sensitive: a computational position
calls `leb` by name, which is exactly the split
`issues/le-named-proposition.md` landed. `>=` and `>` are not added; an
argument-order flip is what `issues/method-receiver-position.md` taught to be
suspicious of, and no use site has asked.

---

## 2. Where it sits, and why not in `infix_op`

The obvious implementation is a fourth row in `infix_op` —
`LtEq => ("Le", 1, 2)` — and it is wrong for one reason: every row in that
table is **left-associative by construction** (`right_bp > left_bp`), so
`a <= b <= c` would silently parse as `Le(Le(a, b), c)`. A proposition
compared against a number is not a reading anyone wants a parser to pick.

The structure that was already there is better. `=` has never been an
`infix_op` row: it is handled in `Parser::expr`, *above* the
precedence-climbing loop, and made non-associative by reading its right
operand with the `no_eq` suppression flag set. So `=` was already a
non-associative level looser than all arithmetic — which is precisely the
level a comparison wants.

So `<=` joins `=` there rather than joining `+` in the table, and `<` moves
**out** of the table to join them:

```
comparison  :=  arith (("=" | "<=" | "<") arith)?      -- one rung, no chaining
arith       :=  … "+" … "*" … postfix … atom           -- infix_op, left-assoc
```

Three consequences, each of which is the point:

- **Looser than arithmetic, for free.** `a + b <= c * d` is
  `Le(add(a, b), mul(c, d))`; the rung's operands are whole `expr_bp(0)`
  parses. No binding-power number had to be chosen, and none can drift.
- **Tighter than `->`, for free.** `Parser::expr` handles the arrow after the
  comparison, so `n <= m -> P` is `Le(n, m) -> P` and the kit's arrow chains
  restate verbatim.
- **`<` stops chaining too.** It was `("lt", 1, 2)`, so `a < b < c` used to
  build `lt(lt(a, b), c)`. It now shares the rung and is rejected. `lt` is
  still the desugar target and still has no definition anywhere — moving it
  costs nothing and buys coherence, and the speculative type-argument parse
  (`docs/surface-polymorphism.md` §1) is untouched, since `try_tyargs` runs in
  `postfix`, below both.

`Lt(n, m) := Le(Succ(n), m)` is a **one-row follow-on**, not part of this
round: the desugaring is already in place, so landing `<` properly is a
definition in `lib/` and a redirect of the `"lt"` string. Nothing asks for it
yet.

---

## 3. Non-associativity, and the one place it stops short

Rejection is structural first. The right operand is read with `no_eq` set, so
it is an *arithmetic* expression and cannot grow a comparison of its own; a
second comparison is therefore left dangling. Dangling would surface as
whatever error the caller raised next ("expected `{`"), so the rung checks for
it and says what happened:

```
error: parse error: comparisons do not chain: `=`, `<=` and `<` share one
non-associative level, so `a <= b <= c` has no reading. Write the two
comparisons separately, or parenthesise the one that is meant to be an operand
  --> chain.hthr:1:45
  |
1 | theorem t(a: Nat, b: Nat, c: Nat, h: a <= b <= c): a = a { refl }
  |                                             ^^
```

`a <= b == c` gets the same message plus the standing `==`-is-not-Heather
hint. `a = b <= c` and `a < b <= c` get it too — one rung means one rule.

**There used to be an exception for a trailing `=`** — after a comparison, an
`=` could be punctuation rather than an operator, because
`let p: a = b = pf;` and `let h: n <= m = pf;` put an annotated `let`'s binder
exactly there, and the parser could not tell those from a chain without
deciding `issues/annotated-let-swallows-the-equals.md`.

**Gone as of 2026-08-02** (`docs/let-and-blocks-design.md` §3): the annotation
position now reads its type with the whole comparison rung suppressed, so a
`=` after a completed comparison is *always* a chain and gets the same
message as `<=` and `==`. An equality annotation is parenthesised —
`let p: (a = b) = pf;` — which is the escape hatch the `CHAIN` message already
advised and, until that round, did not actually have.

Worth recording, since this section predicted otherwise: **it was not `:=`
that removed the exception.** Keeping `=` as the `let` binder and suppressing
the rung in the annotation delivers the same diagnostic at a sixth of the
migration cost, and leaves `:=` free for `issues/effects-direction.md`.

---

## 4. The lexer

`"<=" => LtEq` goes in the two-byte match, ahead of `'<' => Lt`. The generics
worry is that greedy two-byte lexing steals a `<` from a type-argument list —
and it cannot, because a type-argument list is `<` followed by a *type*, and
no type starts with `=`. `Foo<=` is not a program before this round and is not
one after it. The speculative tyarg parse never sees an `LtEq` at all: it bails
on its first `self.ty()`, restores the position, and the token is still there
for the comparison rung.

Pinned by `parser::tests::a_type_argument_list_survives_the_two_char_token`
and `operators::generics_and_le_share_a_file` — a generic record, a generic
`fn`, an explicit type application, and a `<=` in one file.

---

## 5. What it bought

`lib/ir_v1.hthr` restates its ordering statements: `fuel_monotone`'s `hle`,
`conv_loosen`'s, `add_equiv_at`'s, and the results of `le_refl`, `le_succ_r`,
`le_add`, `le_add_l`, `le_add_r`. Doc §6's `simulate(…) = Out(vs) -> n <= m ->
simulate(…) = Out(vs)` is now verbatim in both shape and spelling.

Explicit `Le` is **kept inside explicit motives** (`match n as λ z =>
(m: Nat) -> Le(z, m) -> …`). A motive is already dense with binders the reader
has to track; an infix operator there reads as one more thing to disentangle,
not one fewer. The rule of thumb: `<=` where the order is being *stated*, `Le`
where it is being *generalized over*.
